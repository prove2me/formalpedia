-- Prove2me | Definitions.Def_KedlayaUmans_Multimodular_ExtensionRing
-- name    : KedlayaUmans_Multimodular_ExtensionRing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:15.490363+00:00
-- url     : https://prove2.me/theorems/3d00961e-757e-42cb-aaef-96427db5e4c2
-- title:
--   Algorithm MULTIMODULAR-FOR-EXTENSION-RING over $(\mathbb Z/r\mathbb Z)[Z]/(E(Z))$ (Section 4.3)
-- statement:
--   Let $r \ge 1$, let $E(Z) \in (\mathbb Z/r\mathbb Z)[Z]$ be monic of degree $e$, and let $R = (\mathbb Z/r\mathbb Z)[Z]/(E(Z))$. Each $x \in R$ has a canonical representative of degree at most $e-1$, its remainder modulo $E$. Its **lift** $\tilde x \in \mathbb Z[Z]$ is that representative with each coefficient replaced by its representative in $\{0,\dots,r-1\}$. Let $f \in R[X_0,\dots,X_{m-1}]$ have degree at most $d-1$ in each variable, and put
--   $$M = d^m\bigl(e(r-1)\bigr)^{(d-1)m+1} + 1, \qquad r' = M^{(e-1)dm+1}.$$
--   For one point $\alpha \in R^m$ and $t \ge 1$ rounds, **Algorithm MULTIMODULAR-FOR-EXTENSION-RING** does the following.
--
--   1. Lift $f$ to $\tilde f \in \mathbb Z[Z][X_0,\dots,X_{m-1}]$ coefficientwise, and $\alpha$ to $\tilde\alpha \in \mathbb Z[Z]^m$ coordinatewise.
--   2. Reduce modulo $r'$ and $Z - M$, that is, apply $P(Z) \mapsto P(M) \bmod r'$, to obtain $\bar f \in (\mathbb Z/r'\mathbb Z)[X_0,\dots,X_{m-1}]$ and $\bar\alpha \in (\mathbb Z/r'\mathbb Z)^m$.
--   3. Run Algorithm MULTIMODULAR on $(\bar f, \bar\alpha, r', t)$ with the same $d$, obtaining $\beta \in \mathbb Z/r'\mathbb Z$.
--   4. Write the representative $n \in \{0,\dots,r'-1\}$ of $\beta$ in base $M$, form $Q(Z) = \sum_{j=0}^{(e-1)dm} c_j Z^j$ with $c_j = \lfloor n/M^j\rfloor \bmod M$, and return the reduction of $Q$ modulo $r$ and $E(Z)$, an element of $R$.
--
--   When $M \ge 2$, $Q$ is the unique polynomial of degree at most $(e-1)dm$ with coefficients in $\{0,\dots,M-1\}$ such that $Q(M) \equiv \beta \pmod{r'}$, as the paper requires. The algorithm extends multipoint evaluation from $\mathbb Z/r\mathbb Z$ to every ring of this form, in particular to every finite field.
--
--   **Formalization Note** $R$ is `AdjoinRoot E`, the canonical representative is `AdjoinRoot.modByMonicHom`, and $e$ is `E.natDegree`. $r'$ is the value printed on p. 15, $M^{(e-1)dm+1}$; p. 16 prints $M^{(e-1)(d-1)m+1}$ instead. Step 4 computes $Q$ from $\beta$ alone. The running time is not formalized.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (version of Aug. 31, 2008), p. 15, Section 4.3, Algorithm MULTIMODULAR-FOR-EXTENSION-RING

import Mathlib
import Definitions.Def_KedlayaUmans_Multimodular_Algorithm

namespace KedlayaUmans.Multimodular

open Polynomial

/-- The integer lift of a polynomial over `ℤ/rℤ`: each coefficient is replaced by its
representative in `{0, …, r-1}` (the degree does not increase). -/
noncomputable def liftZPoly {r : ℕ} (p : (ZMod r)[X]) : ℤ[X] :=
  ∑ i ∈ p.support, monomial i (((p.coeff i).val : ℕ) : ℤ)

/-- The lift of `x ∈ R = (ℤ/rℤ)[Z]/(E(Z))` to `ℤ[Z]`: the canonical representative of `x` of
degree at most `e - 1` (its remainder modulo the monic `E`), with coefficients lifted to
`{0, …, r-1}`. -/
noncomputable def liftElt {r : ℕ} {E : (ZMod r)[X]} (hE : E.Monic) (x : AdjoinRoot E) : ℤ[X] :=
  liftZPoly (AdjoinRoot.modByMonicHom hE x)

/-- Step 1 of MULTIMODULAR-FOR-EXTENSION-RING: `f̃ ∈ ℤ[Z][X₀, …, X_{m-1}]`, each coefficient of
`f ∈ R[X₀, …, X_{m-1}]` replaced by its lift (`liftElt`). -/
noncomputable def liftPolyExt {r m : ℕ} {E : (ZMod r)[X]} (hE : E.Monic)
    (f : MvPolynomial (Fin m) (AdjoinRoot E)) : MvPolynomial (Fin m) ℤ[X] :=
  ∑ s ∈ f.support, MvPolynomial.monomial s (liftElt hE (f.coeff s))

/-- Step 1 of MULTIMODULAR-FOR-EXTENSION-RING: `α̃ ∈ ℤ[Z]^m`, coordinatewise lift of `α ∈ R^m`. -/
noncomputable def liftPointExt {r m : ℕ} {E : (ZMod r)[X]} (hE : E.Monic)
    (α : Fin m → AdjoinRoot E) : Fin m → ℤ[X] :=
  fun i => liftElt hE (α i)

/-- `M = d^m (e(r-1))^{(d-1)m+1} + 1`. -/
def bigM (d m e r : ℕ) : ℕ := d ^ m * (e * (r - 1)) ^ ((d - 1) * m + 1) + 1

/-- The digit-degree bound `(e-1)dm`. -/
def digitDegree (d m e : ℕ) : ℕ := (e - 1) * d * m

/-- `r′ = M^{(e-1)dm+1}` (the value printed on p. 15). -/
def rPrime (d m e r : ℕ) : ℕ := bigM d m e r ^ (digitDegree d m e + 1)

/-- Step 2: reduction `ℤ[Z] → ℤ/r′ℤ` modulo `r′` and `Z - M`, i.e. `P(Z) ↦ P(M) mod r′`. -/
noncomputable def evalAtM (M r' : ℕ) : ℤ[X] →+* ZMod r' :=
  Polynomial.eval₂RingHom (Int.castRingHom (ZMod r')) (M : ZMod r')

/-- Step 4: the polynomial `Q(Z) = ∑_{j=0}^{D} c_j Z^j` whose coefficients `c_j = ⌊n / M^j⌋ mod M`
are the base-`M` digits of `n` (the unique polynomial of degree at most `D` with coefficients in
`{0, …, M-1}` and `Q(M) ≡ n (mod M^{D+1})`, when `M ≥ 2`). -/
noncomputable def digitPoly (M D n : ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range (D + 1), C (((n / M ^ j) % M : ℕ) : ℤ) * X ^ j

/-- **Algorithm MULTIMODULAR-FOR-EXTENSION-RING** (Kedlaya–Umans, §4.3, p. 15), for one evaluation
point `α ∈ R^m`, where `R = (ℤ/rℤ)[Z]/(E(Z))`, `E` monic of degree `e`, and `t` is the number of
rounds.  With `M = d^m (e(r-1))^{(d-1)m+1} + 1` and `r′ = M^{(e-1)dm+1}`:

1. lift `f` and `α` to `f̃ ∈ ℤ[Z][X]`, `α̃ ∈ ℤ[Z]^m`;
2. reduce modulo `r′` and `Z - M`, obtaining `f̄ ∈ (ℤ/r′ℤ)[X]` and `ᾱ ∈ (ℤ/r′ℤ)^m`;
3. `β = MULTIMODULAR(f̄, ᾱ, r′, t)` (with the same `d`);
4. form `Q(Z)` from the base-`M` digits of `β ∈ {0, …, r′-1}` and return `Q` reduced modulo
   `r` and `E(Z)`. -/
noncomputable def multimodularExt (d t : ℕ) {r m : ℕ} {E : (ZMod r)[X]} (hE : E.Monic)
    (f : MvPolynomial (Fin m) (AdjoinRoot E)) (α : Fin m → AdjoinRoot E) : AdjoinRoot E :=
  let e : ℕ := E.natDegree
  let M : ℕ := bigM d m e r
  let r' : ℕ := rPrime d m e r
  let fbar : MvPolynomial (Fin m) (ZMod r') := MvPolynomial.map (evalAtM M r') (liftPolyExt hE f)
  let αbar : Fin m → ZMod r' := fun i => evalAtM M r' (liftPointExt hE α i)
  let β : ZMod r' := multimodular d t r' fbar αbar
  let Q : ℤ[X] := digitPoly M (digitDegree d m e) β.val
  AdjoinRoot.mk E (Q.map (Int.castRingHom (ZMod r)))

end KedlayaUmans.Multimodular


