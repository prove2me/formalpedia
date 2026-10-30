-- Prove2me | Definitions.Def_KUMultimodular_multimodularExt
-- name    : KUMultimodular_multimodularExt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:59:08.903084+00:00
-- url     : https://prove2.me/theorems/3446b7c4-62ed-4b5e-a162-9700455fc382
-- title:
--   Algorithm MULTIMODULAR-FOR-EXTENSION-RING over $(\mathbb Z/r\mathbb Z)[Z]/(E(Z))$
-- statement:
--   Let $r \ge 1$, let $E \in (\mathbb Z/r\mathbb Z)[Z]$ be monic of degree $e$, and let $R = (\mathbb Z/r\mathbb Z)[Z]/(E(Z))$, a finite ring of cardinality $q = r^e$. Let $f \in R[X_0,\dots,X_{m-1}]$ have degree at most $d-1$ in each variable, let $\alpha_0,\dots,\alpha_{N-1} \in R^m$, and let $t \ge 1$. Put
--   $$M = d^m\,(e(r-1))^{(d-1)m+1} + 1, \qquad r' = M^{(e-1)dm+1}.$$
--   **Algorithm MULTIMODULAR-FOR-EXTENSION-RING**:
--
--   1. Lift every coefficient of $f$ and every coordinate of every $\alpha_i$ to a polynomial in $\mathbb Z[Z]$ of degree at most $e-1$ with coefficients in $\{0,\dots,r-1\}$ (the canonical representative modulo $E$), giving $\tilde f$ and $\tilde\alpha_i$.
--   2. Reduce $\tilde f$ and the $\tilde\alpha_i$ modulo $r'$ and $Z - M$, i.e. replace each lifted element $g(Z)$ by $g(M) \bmod r'$, giving $\bar f \in (\mathbb Z/r'\mathbb Z)[X]$ and $\bar\alpha_i \in (\mathbb Z/r'\mathbb Z)^m$.
--   3. Run MULTIMODULAR over $\mathbb Z/r'\mathbb Z$ with $t$ rounds to compute $\beta_i = \bar f(\bar\alpha_i)$.
--   4. For each $i$, compute the polynomial $Q_i \in \mathbb Z[Z]$ of degree at most $(e-1)dm$ with coefficients in $\{0,\dots,M-1\}$ such that $Q_i(M) \equiv \beta_i \pmod{r'}$ (the $(e-1)dm+1$ base-$M$ digits of $\beta_i$), and return the reduction of $Q_i$ modulo $r$ and $E(Z)$.
--
--   This is a Kronecker-type substitution $Z \mapsto M$ that turns evaluation over the extension ring into evaluation over $\mathbb Z/r'\mathbb Z$; $M$ is larger than every coefficient of $\tilde f(\tilde\alpha_i)$, so the base-$M$ digits recover it. In particular it handles every finite field $\mathbb F_q$.
--
--   **Formalization Note** $R$ is `AdjoinRoot E` with `hE : E.Monic`, $e$ is `E.natDegree`; the lift of $x$ is read off `AdjoinRoot.modByMonicHom hE x` (`liftCoeffs`, `liftPoly`). `bigM r e m d` and `rPrime r e m d` are $M$ and $r'$; they are computed in the algorithm with `powC` (repeated squaring). Step 3 calls `mmCore ellC` on the lists of residues modulo $r'$, which is MULTIMODULAR after its Step 1 (the lifts are already in $\{0,\dots,r'-1\}$). The exponent of $r'$ is the one of p. 15; p. 16 prints $M^{(e-1)(d-1)m+1}$, with which Step 4 would not have enough digits when $e \ge 2$.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (2008), §4.3, Algorithm MULTIMODULAR-FOR-EXTENSION-RING, p. 15

import Mathlib
import Definitions.Def_KUMultimodular_Timed
import Definitions.Def_KUMultimodular_densePoly
import Definitions.Def_KUMultimodular_multimodular

namespace KUMultimodular

/-! # Algorithm MULTIMODULAR-FOR-EXTENSION-RING (Kedlaya–Umans, Dagstuhl Seminar Proceedings
08381 (2008), §4.3, p. 15)

The ring is `R = (ℤ/rℤ)[Z]/(E(Z))` with `E` monic of degree `e`, encoded as `AdjoinRoot E`; it has
cardinality `q = r^e`. An element of `R` is represented by its `e` coefficients, i.e. by its
canonical lift, the remainder modulo `E` of degree `≤ e - 1`, with coefficients lifted to
`{0, …, r-1}`. -/

/-- `M = d^m (e(r-1))^{(d-1)m+1} + 1` (p. 15). -/
def bigM (r e m d : ℕ) : ℕ := d ^ m * (e * (r - 1)) ^ ((d - 1) * m + 1) + 1

/-- `r' = M^{(e-1)dm+1}` (p. 15). -/
def rPrime (r e m d : ℕ) : ℕ := bigM r e m d ^ ((e - 1) * d * m + 1)

/-- The lift of `x ∈ (ℤ/rℤ)[Z]/(E(Z))`: the coefficients of `Z^0, …, Z^{e-1}` of its canonical
representative of degree `≤ e - 1`, each lifted to `{0, …, r-1}`. -/
noncomputable def liftCoeffs {r : ℕ} {E : Polynomial (ZMod r)} (hE : E.Monic) (x : AdjoinRoot E) :
    List ℕ :=
  (List.range E.natDegree).map (fun j => ((AdjoinRoot.modByMonicHom hE x).coeff j).val)

/-- The lift of `x` as a polynomial in `ℕ[Z]` of degree `≤ e - 1` with coefficients in
`{0, …, r-1}` (Step 1, p. 15). -/
noncomputable def liftPoly {r : ℕ} {E : Polynomial (ZMod r)} (hE : E.Monic) (x : AdjoinRoot E) :
    Polynomial ℕ :=
  ∑ j ∈ Finset.range E.natDegree,
    Polynomial.monomial j ((AdjoinRoot.modByMonicHom hE x).coeff j).val

/-- Reading the lift of an input element (its `e` coefficients), charged their bit size. -/
noncomputable def liftC {r : ℕ} {E : Polynomial (ZMod r)} (hE : E.Monic) (x : AdjoinRoot E) :
    Timed (List ℕ) :=
  ⟨liftCoeffs hE x, lsize (liftCoeffs hE x) + 1⟩

/-- The reduction modulo `E(Z)` of the polynomial `Σ_j cs_j Z^j ∈ (ℤ/rℤ)[Z]` (Figure 1
"Remainder", p. 8). Charged `ql` of the bit size of the input coefficients, of the input read
as `cs.length` residues of full width `bits r` (the arithmetic of the reduction acts on full-width
residues even when the input digits are small), of `E` and of the output. -/
noncomputable def polyRemC {r : ℕ} (E : Polynomial (ZMod r)) (cs : List ℕ) : Timed (AdjoinRoot E) :=
  ⟨AdjoinRoot.mk E (∑ j ∈ Finset.range cs.length, Polynomial.monomial j ((cs.getD j 0 : ℕ) : ZMod r)),
    ql (lsize cs + (cs.length + 2 * E.natDegree + 1) * bits r)⟩

/-- **Algorithm MULTIMODULAR-FOR-EXTENSION-RING(f, α_0, …, α_{N-1}, t)** (Kedlaya–Umans 2008, §4.3,
p. 15). Input: a monic `E ∈ (ℤ/rℤ)[Z]` of degree `e`, the coefficient table `coef` of
`f ∈ R[X_0, …, X_{m-1}]` (`R = (ℤ/rℤ)[Z]/(E)`) with degree at most `d - 1` in each variable, the
points `α_0, …, α_{N-1} ∈ R^m`, and the number of rounds `t ≥ 1`.
* compute `M = d^m (e(r-1))^{(d-1)m+1} + 1` and `r' = M^{(e-1)dm+1}`;
* Step 1: lift every coefficient and coordinate to `ℤ[Z]` (degree `≤ e - 1`, coefficients in
  `{0, …, r-1}`);
* Step 2: reduce modulo `r'` and `Z - M`, i.e. evaluate each lift at `Z = M` modulo `r'`;
* Step 3: run MULTIMODULAR over `ℤ/r'ℤ` with `t` rounds, giving `β_i`;
* Step 4: write `β_i` in base `M` with `(e-1)dm + 1` digits (the polynomial `Q_i`), reduce the
  digits modulo `r` and the polynomial modulo `E(Z)`. -/
noncomputable def multimodularExt (t : ℕ) {r : ℕ} (E : Polynomial (ZMod r)) (hE : E.Monic)
    {m d N : ℕ} (coef : (Fin m → Fin d) → AdjoinRoot E) (α : Fin N → Fin m → AdjoinRoot E) :
    Timed (Fin N → AdjoinRoot E) := do
  let e := E.natDegree
  tick (bits e + bits r)
  -- `M = d^m (e(r-1))^{(d-1)m+1} + 1`
  let rm1 ← subC r 1
  let er ← mulC e rm1
  let dPow ← powC d m
  let dm1 ← subC d 1
  let x1 ← mulC dm1 m
  let ex ← addC x1 1
  let pw ← powC er ex
  let M0 ← mulC dPow pw
  let M ← addC M0 1
  -- `K = (e-1)dm + 1` and `r' = M^K`
  let e1 ← subC e 1
  let y1 ← mulC e1 d
  let y2 ← mulC y1 m
  let K ← addC y2 1
  let r' ← powC M K
  -- Step 1: lifts
  let cl ← mapT (fun a => liftC hE (coef a)) (lexEnum d m)
  let al ← mapT (fun i => mapT (fun j => liftC hE (α i j)) (List.finRange m)) (List.finRange N)
  -- Step 2: reduction modulo `r'` and `Z - M`
  let cs ← mapT (fun l => evalAtModC l M r') cl
  let pts ← mapT (fun a => mapT (fun l => evalAtModC l M r') a) al
  -- Step 3: MULTIMODULAR over `ℤ/r'ℤ` with `t` rounds
  let β ← mmCore ellC m d (t - 1) r' cs pts
  -- Step 4: base-`M` digits, reduction modulo `r` and `E(Z)`
  let out ← mapT (fun b => do
      let ds ← radixC b M K
      let ds' ← mapT (fun x => do
          let qr ← divModC x r
          pure qr.2) ds
      polyRemC E ds') β
  pure (fun i => out.getD i 0)

end KUMultimodular


