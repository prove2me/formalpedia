-- Prove2me | Definitions.Def_Random2SATWindow_CriticalLaw_Hadamard
-- name    : Random2SATWindow_CriticalLaw_Hadamard
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:40:44.908596+00:00
-- url     : https://prove2.me/theorems/ce0322de-4071-4d17-9b4c-8d5efdd4aa76
-- title:
--   Exponential Hadamard products, $D_0$, $I_0$, $S_\varphi$, $\ddot{\mathrm{SAT}}_\varphi$, $S(z,w;y)$, $S_r$, $S_0$, $B_0$ and $H_n(x,y)$
-- statement:
--   §5.1.1 (printed pp. 23–25). Series are formal power series in $z$ over a commutative $\mathbb Q$-algebra $K$ containing the weight $w$, with $1+w$ a unit; `Ring.inverse (1+w)` is $(1+w)^{-1}$.
--
--   * `expOf f` $=e^{f}$, the formal substitution of $f$ (zero constant term) into $\exp$; `doubleArg f` $=f(2z)$; `invFact k` $=1/k!$.
--   * Exponential Hadamard product: $\big(\sum u_kz^k/k!\big)\odot\big(\sum v_kz^k/k!\big)=\sum u_kv_kz^k/k!$, i.e. $[z^k](f\odot g)=k!\,[z^k]f\,[z^k]g$ (`expHadamard`).
--   * (46) $D_0(z,w)=\sum_{k\ge0}\dfrac{z^k}{k!(1+w)^{\binom k2}}$, $I_0(z,w)=\sum_{k\ge0}\dfrac{z^k}{2^kk!(1+w)^{k(k-1)}}$.
--   * A simple digraph on $[k]$ is an arc set $E\subseteq[k]\times[k]$ without loops; `IsSimpleSC k E` adds strong connectivity. `IsDigraphWeight φ`: $\varphi$ (values in $K$) is invariant under relabelling $[k]$ and under reversing all arcs, on simple strongly connected digraphs.
--   * Lemma 5.2: $S_\varphi(z,w)=\sum_{k\ge1}\frac{z^k}{k!}\sum_C\varphi(C)w^{e(C)}$, $C$ over the simple strongly connected digraphs on $[k]$ (`SPhi`). For a formula $F$, $\varphi(F)=\prod_{\{C,\bar C\}\in O(F)}\varphi(C)$ (`phiFormula`), $\varphi(C)$ evaluated on the subdigraph of $D(F)$ induced by $C$, relabelled onto $[|C|]$ (`inducedArcs`); `mirrorSet`, `mirrorOrbits` $=O(F)$ (5), `orbitRep` picks a member of an orbit. $\ddot{\mathrm{SAT}}_\varphi(z,w)=\sum_n\frac{z^n}{2^nn!(1+w)^{n(n-1)}}\sum_{F\in\mathrm{SAT}_n}\varphi(F)w^{|F|}$ (`SATPhi`).
--   * (48), (50): with $\varphi(C)=y^{r(C)}$ over $\mathbb R[y]$ (`excessWeight`), $S(z,w;y)=S_0+\sum_{r\ge1}y^rS_r$ is `SExcess w` (real $w$). $S_r$ (`SExcessR r w`): the EGF of simple strongly connected digraphs of excess $r\ge1$, $z$ marking vertices and $w$ arcs. (47) $S_0(z,w)=z+\sum_{k\ge2}(wz)^k/k$ (`S0`).
--   * $B_0(z,w)=e^{-S_0(z,w)}\odot D_0(z,w)$ (`B0Series`), and `B0 z w` its sum at complex $z$ (entire for $w>0$: the coefficients carry $(1+w)^{-\binom k2}$).
--   * (51) $H_n(x,y)=\sum_{q\ge0}p_{n,q}(x)y^q$ (`Hpoly`, a polynomial: $R(F)\le|F|\le N_n$).
--
--   **Formalization Note.** The relabelling of an SCC onto $[|C|]$ and the orbit representative are chosen non-constructively; for a weight satisfying `IsDigraphWeight` the value does not depend on the choice (relabelling invariance, and complementing literals maps $\bar C$ onto the reversal of $C$). A weight defined only on simple strongly connected digraphs is extended arbitrarily: only those values enter $S_\varphi$ and $\varphi(F)$.
-- source:
--   Ravelomanana, Inside the Critical Window of Random 2-SAT, STOC 2027 submission (manuscript sha256 eef2fa67…), §5.1.1, (46)–(51), printed pp. 23–25 (PDF 25–27); (87), printed p. 38 (PDF 40)

import Mathlib
import Definitions.Def_Random2SATWindow_CriticalLaw_Formulas

set_option autoImplicit false

open scoped BigOperators

namespace Random2SATWindow.CriticalLaw

/-! # Exponential Hadamard products and the implication generating functions

Ravelomanana, *Inside the Critical Window of Random 2-SAT*, STOC 2027 submission (manuscript
sha256 eef2fa67…), §5.1.1, (46)–(51), printed pp. 23–25 (PDF 25–27); (87), printed p. 38
(PDF 40).

Coefficient ring. All series are formal power series in `z` over a commutative `ℚ`-algebra `K`
that contains the clause-weight `w`, with `1 + w` a unit of `K` (so that `(1+w)^{-C(k,2)}` makes
sense). Taking `K = A⟦w⟧` (with `w = X`) gives the series in a formal `w` over a `ℚ`-algebra `A`;
taking `K = ℝ[y]` with a real `w > 0` gives the specialization used in (51).

A simple digraph on `[k]` is a set of arcs `E ⊆ [k] × [k]` without loops (no multiple arcs by
construction); it is strongly connected when every vertex reaches every other. -/

section Series

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- The exponential of a power series with zero constant term, `e^f = exp ∘ f`
(formal substitution into `exp`). -/
noncomputable def expOf (f : PowerSeries K) : PowerSeries K :=
  PowerSeries.subst f (PowerSeries.exp K)

/-- `1/k!` in `K`. -/
noncomputable def invFact (k : ℕ) : K := algebraMap ℚ K ((k.factorial : ℚ)⁻¹)

/-- The exponential Hadamard product:
`(Σ u_k z^k/k!) ⊙ (Σ v_k z^k/k!) = Σ u_k v_k z^k/k!`, i.e. `[z^k](f ⊙ g) = k! [z^k]f [z^k]g`. -/
noncomputable def expHadamard (f g : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun k => (k.factorial : K) * PowerSeries.coeff k f * PowerSeries.coeff k g

/-- `D_0(z, w) = Σ_{k ≥ 0} z^k / (k! (1+w)^{C(k,2)})` (46). -/
noncomputable def D0 (w : K) : PowerSeries K :=
  PowerSeries.mk fun k => invFact k * Ring.inverse (1 + w) ^ k.choose 2

/-- `I_0(z, w) = Σ_{k ≥ 0} z^k / (2^k k! (1+w)^{k(k-1)})` (46). -/
noncomputable def I0 (w : K) : PowerSeries K :=
  PowerSeries.mk fun k => algebraMap ℚ K ((2 : ℚ) ^ k)⁻¹ * invFact k *
    Ring.inverse (1 + w) ^ (k * (k - 1))

/-- `f(2z)`. -/
noncomputable def doubleArg (f : PowerSeries K) : PowerSeries K :=
  PowerSeries.rescale (2 : K) f

end Series

/-- A simple strongly connected digraph on `[k] = Fin k`, given by its arc set: no loops, and
every vertex reaches every vertex along arcs. -/
def IsSimpleSC (k : ℕ) (E : Finset (Fin k × Fin k)) : Prop :=
  (∀ i, (i, i) ∉ E) ∧ ∀ i j, Relation.ReflTransGen (fun a b => (a, b) ∈ E) i j

/-- A weight `φ` on finite simple strongly connected digraphs, invariant under isomorphism
(relabelling of `[k]`) and under reversal of all arcs (Lemma 5.2). `φ` is a function on all arc
sets of `[k]`, but only its values on simple strongly connected digraphs are constrained (and
only those values enter `S_φ` and `φ(F)`). -/
def IsDigraphWeight {K : Type*} (φ : (k : ℕ) → Finset (Fin k × Fin k) → K) : Prop :=
  (∀ k (E : Finset (Fin k × Fin k)) (π : Equiv.Perm (Fin k)), IsSimpleSC k E →
      φ k (E.map (Equiv.prodCongr π π).toEmbedding) = φ k E) ∧
  (∀ k (E : Finset (Fin k × Fin k)), IsSimpleSC k E →
      φ k (E.map (Equiv.prodComm _ _).toEmbedding) = φ k E)

section Weighted

variable {K : Type*} [CommRing K] [Algebra ℚ K]

open Classical in
/-- `S_φ(z, w) = Σ_{k ≥ 1} (z^k/k!) Σ_C φ(C) w^{e(C)}`, `C` over the simple strongly connected
digraphs on `[k]` (Lemma 5.2). -/
noncomputable def SPhi (φ : (k : ℕ) → Finset (Fin k × Fin k) → K) (w : K) : PowerSeries K :=
  PowerSeries.mk fun k => if k = 0 then 0 else
    invFact k * ∑ E ∈ (Finset.univ : Finset (Finset (Fin k × Fin k))).filter (IsSimpleSC k),
      φ k E * w ^ E.card

open Classical in
/-- The subdigraph of `D(F)` induced by a set `C` of literals, relabelled onto `[|C|]` by a
bijection `C ≃ Fin |C|` (the choice is irrelevant for an isomorphism-invariant weight). -/
noncomputable def inducedArcs {n : ℕ} (F : Formula n) (C : Finset (Literal n)) :
    Finset (Fin C.card × Fin C.card) :=
  Finset.univ.filter fun p =>
    ImplArc F (C.equivFin.symm p.1).1 (C.equivFin.symm p.2).1

/-- The mirror image `C̄ = m(C)` of a set of literals. -/
def mirrorSet {n : ℕ} (C : Finset (Literal n)) : Finset (Literal n) :=
  C.map ⟨Literal.compl, fun u v h => by
    simpa [Literal.compl, Prod.ext_iff] using h⟩

open Classical in
/-- The mirror orbits `O(F) = {{C, C̄} : C ∈ SCC(D(F))}` (5). -/
noncomputable def mirrorOrbits {n : ℕ} (F : Formula n) : Finset (Finset (Finset (Literal n))) :=
  (sccs F).image fun C => {C, mirrorSet C}

open Classical in
/-- A representative of a mirror orbit (any member; on `SAT` both members carry the same weight,
since complementing the literals maps `C̄` onto the reversal of `C`). -/
noncomputable def orbitRep {n : ℕ} (O : Finset (Finset (Literal n))) : Finset (Literal n) :=
  if h : O.Nonempty then h.choose else ∅

/-- `φ(F) = ∏_{{C, C̄} ∈ O(F)} φ(C)`, `φ(C)` evaluated on the subdigraph of `D(F)` induced by `C`
(Lemma 5.2). -/
noncomputable def phiFormula (φ : (k : ℕ) → Finset (Fin k × Fin k) → K) {n : ℕ}
    (F : Formula n) : K :=
  ∏ O ∈ mirrorOrbits F, φ (orbitRep O).card (inducedArcs F (orbitRep O))

open Classical in
/-- `S̈AT_φ(z, w) = Σ_{n ≥ 0} z^n / (2^n n! (1+w)^{n(n-1)}) Σ_{F ∈ SAT_n} φ(F) w^{|F|}`
(Lemma 5.2). -/
noncomputable def SATPhi (φ : (k : ℕ) → Finset (Fin k × Fin k) → K) (w : K) : PowerSeries K :=
  PowerSeries.mk fun n => algebraMap ℚ K ((2 : ℚ) ^ n)⁻¹ * invFact n *
    Ring.inverse (1 + w) ^ (n * (n - 1)) *
    ∑ F ∈ (Finset.univ : Finset (Formula n)).filter Satisfiable, phiFormula φ F * w ^ F.card

end Weighted

open Classical in
/-- The excess weight of §5.1.1: `φ(C) = y^{r(C)}`, `r(C) = (e(C) - v(C))_+`, with `y` the
variable of `ℝ[y]`; with it `S_φ = S(z, w; y)` of (48) and `φ(F) = y^{R(F)}` on `SAT`. -/
noncomputable def excessWeight (k : ℕ) (E : Finset (Fin k × Fin k)) : Polynomial ℝ :=
  Polynomial.X ^ ((E.card : ℤ) - (k : ℤ)).toNat

/-- `S(z, w; y) = S_0(z, w) + Σ_{r ≥ 1} y^r S_r(z, w)` (48), over `ℝ[y]`, for a real `w`. -/
noncomputable def SExcess (w : ℝ) : PowerSeries (Polynomial ℝ) :=
  SPhi excessWeight (Polynomial.C w)

/-- `H_n(x, y) = Σ_{q ≥ 0} p_{n,q}(x) y^q` (51), a polynomial in `y` (`p_{n,q} = 0` for
`q > N_n`). -/
noncomputable def Hpoly (n : ℕ) (x : ℝ) : Polynomial ℝ :=
  ∑ q ∈ Finset.range (numClauses n + 1), Polynomial.C (stratumProb n q x) * Polynomial.X ^ q

open Classical in
/-- `S_r(z, w)` (§5.1.1): the EGF of simple strongly connected digraphs of excess `r ≥ 1`,
`z` marking vertices and `w` arcs: `[z^k] S_r = (1/k!) Σ_{C on [k], e(C) - k = r} w^{e(C)}`. -/
noncomputable def SExcessR (r : ℕ) (w : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun k => if k = 0 then 0 else
    invFact k * ∑ E ∈ (Finset.univ : Finset (Finset (Fin k × Fin k))).filter
      (fun E => IsSimpleSC k E ∧ (E.card : ℤ) - k = r), w ^ E.card

/-- `S_0(z, w) = z + Σ_{k ≥ 2} (wz)^k / k = (1 - w) z - log(1 - wz)` (47). -/
noncomputable def S0 (w : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun k => if k = 0 then 0 else if k = 1 then 1 else w ^ k / k

/-- `B_0(z, w) = e^{-S_0(z, w)} ⊙ D_0(z, w)` (§5.1.1 and (87)), as a formal power series in `z`. -/
noncomputable def B0Series (w : ℝ) : PowerSeries ℝ :=
  expHadamard (expOf (-S0 w)) (D0 w)

/-- `B_0(z, w)` as a function of a complex `z` (its series is entire for `w > 0`, since the
coefficients carry the factor `(1+w)^{-C(k,2)}`). -/
noncomputable def B0 (z : ℂ) (w : ℝ) : ℂ :=
  ∑' k : ℕ, ((PowerSeries.coeff k (B0Series w) : ℝ) : ℂ) * z ^ k

end Random2SATWindow.CriticalLaw


