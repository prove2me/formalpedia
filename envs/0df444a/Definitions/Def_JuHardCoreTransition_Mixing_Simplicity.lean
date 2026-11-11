-- Prove2me | Definitions.Def_JuHardCoreTransition_Mixing_Simplicity
-- name    : JuHardCoreTransition_Mixing_Simplicity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:16:42.625032+00:00
-- url     : https://prove2.me/theorems/5093d7aa-61c8-48b8-bedd-f6c75d265d42
-- title:
--   Residual planted matching laws after exposure and the simplicity probability
-- statement:
--   Fix one gadget with base labels $[N]$ and $d$ matching colours. Every label carries a fixed state in a finite set $S$ with a symmetric compatibility relation: for $j=0$ one state, everything compatible ($\xi=(1)$); for $j=1$ the states $\Omega$ with $B$ ($\xi=\alpha$); for $j=2$ the pairs $\Omega^2$ with $B\otimes B$ ($\xi=\Gamma$). A matching edge is **compatible** if it joins compatible states.
--
--   An **exposure** $R$ specifies $q_N$ disjoint edges of the first matching $M_{v,1}$ with their endpoint labels and states. The **residual law** $P^{(j)}_\xi(\cdot\mid R)$ keeps these edges, completes $M_{v,1}$ by a uniform compatible perfect matching of the remaining labels, and chooses each other matching independently and uniformly among compatible perfect matchings of all labels; the exposure is **admissible** when these choices are feasible. Exposed edges need not be compatible and still count when testing simplicity. $X$ counts cycles of length two, each specified by a base edge and two colours containing it; $\{X=0\}$ means no base edge is repeated across colours.
--
--   With $P_\xi$ the entropy-maximising compatible symmetric coupling of marginal $\xi$ and $T_\xi(a,b)=P_\xi(a,b)/\xi_a$, the limiting means are $\Lambda_0=d(d-1)/4$, $\Lambda_1(\alpha)=\frac{d(d-1)}4\operatorname{tr}(T_\alpha^2)$, $\Lambda_2(\Gamma)=\frac{d(d-1)}4\operatorname{tr}((T^{(2)}_\Gamma)^2)$, and $a_j=e^{-\Lambda_j}$.
--
--   **Formalization Note.** An exposure is a `Finset (Fin N × Fin N)` of pairwise disjoint ordered pairs $i\neq i'$ (`IsExposure`). `AdmissibleTuple Bc st R M`: colour $0$ contains every exposed edge and is compatible off the exposed labels, every other colour is compatible everywhere; the residual law is the uniform law on such tuples, so `simpleProb` $=P^{(j)}_\xi(X=0\mid R)$ is a ratio of counts. `IsSimpleTuple M` is $X=0$. `proportions st` is the state-proportion vector $\xi$; `limitMean d Bc ξ` is $\frac{d(d-1)}4\operatorname{tr}(T_\xi^2)$. `IsAdmissibleTypeSet` is a compact set of probability vectors with positive proportions and positive permitted coupling entries; `SimplicityBoundsHold Bc a d K C N₀ Kset` packages the two conclusions of (8.43) and the lower bound $\tfrac12e^{-4d(d-1)}$ for given constants. `qOf (p,q)=p/(q+1)` encodes nonnegative rationals and `boxTypeSet lo hi` is the type set cut out by coordinate bounds.
-- source:
--   Ju, Liu and Yin, Fine-Grained Complexity Across the Computational Phase Transition, arXiv:2611.02702, pinned source.pdf dated 2026-11-02, SHA256 6288a2d2b0acc0256c0a8e1e8ea59eb0fbfff70c6d282c1c83eacf59cecd3678 (arXiv version suffix not supplied; unverified), §8.3 and Lemma 8.12, printed pp.91–92 / PDF pp.92–93

import Mathlib
import Definitions.Def_JuHardCoreTransition_Mixing_GadgetRate

namespace JuHardCoreTransition.Mixing

/-!
# Residual planted matching laws after exposure, and the simplicity probability

Ju, Liu and Yin, *Fine-Grained Complexity Across the Computational Phase Transition*,
arXiv:2611.02702, pinned source.pdf dated 2026-11-02 (SHA256 6288a2d2…3678; arXiv version suffix
not supplied), §8.3 and Lemma 8.12 (printed pp.91–92 / PDF pp.92–93).

One gadget with `N` base labels and `d` matching colours (colour `0` is the first matching
`M_{v,1}`). Every label carries a fixed state `st i ∈ S` in a finite state space `S` with a
compatibility relation `Bc` on states: for `j = 0` a single state with every pair compatible, for
`j = 1` the states `Ω` with `B`, for `j = 2` the pairs `Ω²` with `B ⊗ B`. A matching is
*compatible* when every one of its edges joins compatible states.

An *exposure* `R` is a set of disjoint edges `(i, i')` (`i ≠ i'`) of the first matching, given with
their endpoint labels (and hence states). The residual law `P_ξ^{(j)}(· | R)` keeps these edges in
colour `0`, completes colour `0` by a uniform compatible perfect matching of the remaining labels,
and draws each other colour independently as a uniform compatible perfect matching of all labels.
This is the uniform law on the set of tuples `M : Fin d → PerfMatch N` satisfying these
constraints (`AdmissibleTuple`); the exposure is *admissible* when that set is nonempty. Exposed
edges need not be compatible.

`X` counts cycles of length two: a base edge `{i, i'}` together with two colours both containing
it (exposed edges included). `X = 0` is `IsSimpleTuple`: no base edge appears in two colours.
`simpleProb Bc st d R = P_ξ^{(j)}(X = 0 | R)`.

`limitMean d Bc ξ = d(d−1)/4 · tr(T_ξ²)` is `Λ_j(ξ)`, with `T_ξ` from the entropy-maximising
compatible coupling of marginal `ξ` (`transitionOf`, as in (8.9)).
-/

variable {S : Type*} [Fintype S]

/-- The labels covered by the exposed edges. -/
def exposedLabels {N : ℕ} (R : Finset (Fin N × Fin N)) : Finset (Fin N) :=
  R.image Prod.fst ∪ R.image Prod.snd

/-- `R` is a set of disjoint base edges (each edge listed once, as an ordered pair `i ≠ i'`). -/
def IsExposure {N : ℕ} (R : Finset (Fin N × Fin N)) : Prop :=
  (∀ e ∈ R, e.1 ≠ e.2) ∧
    ∀ e ∈ R, ∀ e' ∈ R, e ≠ e' → e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2

/-- A tuple of `d` matchings in the support of the residual law: colour `0` contains every exposed
edge and is compatible on all unexposed labels; every other colour is a compatible perfect
matching of all labels. -/
def AdmissibleTuple {N d : ℕ} (Bc : S → S → Prop) (st : Fin N → S) (R : Finset (Fin N × Fin N))
    (M : Fin d → PerfMatch N) : Prop :=
  ∀ c : Fin d,
    (c.val = 0 → (∀ e ∈ R, (M c).1 e.1 = e.2) ∧
      ∀ i, i ∉ exposedLabels R → Bc (st i) (st ((M c).1 i))) ∧
    (c.val ≠ 0 → ∀ i, Bc (st i) (st ((M c).1 i)))

/-- `X = 0`: no base edge belongs to two different colours (the union `B_v` is simple). -/
def IsSimpleTuple {N d : ℕ} (M : Fin d → PerfMatch N) : Prop :=
  ∀ i : Fin N, ∀ c c' : Fin d, c ≠ c' → (M c).1 i ≠ (M c').1 i

/-- The exposure `R` is admissible: it is a set of disjoint edges and the residual law is
well defined (some admissible tuple exists). -/
def IsAdmissibleExposure {N : ℕ} (d : ℕ) (Bc : S → S → Prop) (st : Fin N → S)
    (R : Finset (Fin N × Fin N)) : Prop :=
  IsExposure R ∧ ∃ M : Fin d → PerfMatch N, AdmissibleTuple Bc st R M

/-- `P_ξ^{(j)}(X = 0 | R)`: the probability, under the uniform law on admissible tuples, that no
base edge is repeated across colours. -/
noncomputable def simpleProb {N : ℕ} (Bc : S → S → Prop) (st : Fin N → S) (d : ℕ)
    (R : Finset (Fin N × Fin N)) : ℝ := by
  classical
  exact ((Finset.univ.filter fun M : Fin d → PerfMatch N =>
      AdmissibleTuple Bc st R M ∧ IsSimpleTuple M).card : ℝ) /
    ((Finset.univ.filter fun M : Fin d → PerfMatch N => AdmissibleTuple Bc st R M).card : ℝ)

/-- The state proportions `ξ_a = #{i : st i = a}/N` of a state assignment. -/
noncomputable def proportions {N : ℕ} [DecidableEq S] (st : Fin N → S) : S → ℝ :=
  fun a => ((Finset.univ.filter fun i => st i = a).card : ℝ) / N

/-- `Λ(ξ) = d(d−1)/4 · tr(T_ξ²)` for the compatibility `Bc`. -/
noncomputable def limitMean (d : ℕ) (Bc : S → S → Prop) (ξ : S → ℝ) : ℝ :=
  (d : ℝ) * ((d : ℝ) - 1) / 4 * Matrix.trace (transitionOf Bc ξ * transitionOf Bc ξ)

/-- A fixed compact set of proportion vectors (probability vectors) on which all state
proportions and all entries of the entropy-maximising coupling permitted by `Bc` are positive. -/
def IsAdmissibleTypeSet (Bc : S → S → Prop) (Kset : Set (S → ℝ)) : Prop :=
  IsCompact Kset ∧ ∀ ξ ∈ Kset, (∑ a, ξ a = 1) ∧ (∀ a, 0 < ξ a) ∧
    ∀ a b, Bc a b → 0 < entMaxCoupling Bc ξ a b

/-- The two conclusions of Lemma 8.12 with constants `C, N₀`, for the limit `a = e^{−Λ}` given as a
function of the proportions: for every even `N ≥ N₀`, every state assignment with proportions in
`Kset`, and every admissible exposure of at most `K√N` edges,
`|log(P(X = 0 | R)/a(ξ))| ≤ C/√N` and `P(X = 0 | R) ≥ ½ e^{−4d(d−1)}`. -/
def SimplicityBoundsHold [DecidableEq S] (Bc : S → S → Prop) (a : (S → ℝ) → ℝ) (d : ℕ)
    (K C : ℝ) (N₀ : ℕ) (Kset : Set (S → ℝ)) : Prop :=
  ∀ N : ℕ, Even N → N₀ ≤ N → ∀ st : Fin N → S, proportions st ∈ Kset →
    ∀ R : Finset (Fin N × Fin N), IsAdmissibleExposure d Bc st R → (R.card : ℝ) ≤ K * Real.sqrt N →
      |Real.log (simpleProb Bc st d R / a (proportions st))| ≤ C / Real.sqrt N ∧
        1 / 2 * Real.exp (-(4 * (d : ℝ) * ((d : ℝ) - 1))) ≤ simpleProb Bc st d R

/-- A nonnegative rational encoded by a pair of naturals: `(p, q) ↦ p/(q+1)`. -/
noncomputable def qOf (x : ℕ × ℕ) : ℝ := (x.1 : ℝ) / ((x.2 : ℝ) + 1)

/-- The compact type set specified by rational coordinate bounds `lo_a ≤ ξ_a ≤ hi_a` on the
probability simplex. -/
def boxTypeSet (lo hi : S → ℝ) : Set (S → ℝ) :=
  {ξ | (∑ a, ξ a = 1) ∧ ∀ a, lo a ≤ ξ a ∧ ξ a ≤ hi a}

end JuHardCoreTransition.Mixing


