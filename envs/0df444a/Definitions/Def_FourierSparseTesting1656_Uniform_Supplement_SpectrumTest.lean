-- Prove2me | Definitions.Def_FourierSparseTesting1656_Uniform_Supplement_SpectrumTest
-- name    : FourierSparseTesting1656_Uniform_Supplement_SpectrumTest
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T13:12:18.406865+00:00
-- url     : https://prove2.me/theorems/33c96959-65c3-42bf-b7b9-446121523577
-- title:
--   SpectrumTest (Algorithm 1) as a nonadaptive query algorithm with a uniform random subspace and two uniform shifts
-- statement:
--   Let $V=\mathbb F_2^n$, let $s\ge1$ be an integer, and set
--   $$d=\min\{n,\lceil\log_2(16s^4)\rceil\}.$$
--   **SpectrumTest** (Algorithm 1) receives oracle access to a Boolean function $f:V\to\{-1,+1\}$ and runs as follows.
--
--   1. It draws a subspace $H\le V$ uniformly among all subspaces of dimension exactly $d$, and two shifts $a,r\in V$, uniform and independent of each other and of $H$. A complement $W$ of the annihilator $H^\perp$ ($V=W\oplus H^\perp$) is chosen by a fixed rule $H\mapsto W$.
--   2. It queries $f$ at every point of the four cosets $H$, $a+H$, $r+H$, $a+r+H$, each enumerated in one fixed order of $H$: $4\cdot 2^d$ queries in all, fixed by $(H,a,r)$ before any answer is read.
--   3. From the answers it computes the restricted spectra $\hat f_{t+H}(\gamma)$, $\gamma\in W$, $t\in\{0,a,r,a+r\}$, and accepts (output $1$) exactly when the sparsity, magnitude, triangle and additive checks of Algorithm 1 all pass; otherwise it rejects (output $0$).
--
--   These are the objects in which Theorem 3.1 is stated; the checks themselves are the mission's published definition of the four checks.
--
--   **Formalization Note** The algorithm is an instance of the referenced nonadaptive query model: a seed space $\{H:\dim H=d\}\times V\times V$ with the uniform law on the discrete $\sigma$-algebra, a query list computed from the seed, and an output computed from the seed and the ordered answer list only. The output rebuilds a Boolean function from the answers (the answer at the first occurrence of a queried point, a fixed default bit elsewhere) and applies the four checks to it; the checks read only the four queried cosets, so the default is never consulted. $\lceil\log_2(16s^4)\rceil$ is the natural number `Nat.clog 2 (16 s^4)`. The file proves that a $d$-dimensional subspace exists for $d\le n$, so the uniform law is well defined.
-- source:
--   Arijit Ghosh, Manmatha Roy, STOC 2027 submission #1656 (October 2026), p. 8, Algorithm 1 (SpectrumTest) and Theorem 3.1; p. 15 (Query Complexity: 4·2^d queries fixed before any answer); PDF SHA256 5374116f8d05176f80f62c5fdaaddae029e1f9e6af853c5a8e1873cb4e83a123

import Mathlib
import Definitions.Def_FourierSparseTesting1656_Uniform_Correction
import Definitions.Def_CyclicForrelation_Even_queryModel

set_option autoImplicit false

namespace FourierSparseTesting1656.Uniform.Supplement

open FourierDimTesting102.Quantum CyclicForrelation.Even FourierSparseTesting1656.Uniform

/-- Algorithm 1, step 1, p.8: the subspace dimension `d = min{n, ⌈log₂(16 s⁴)⌉}`; for the integer
`16 s⁴`, `⌈log₂(16 s⁴)⌉` is `Nat.clog 2 (16 s⁴)`, the least `k` with `16 s⁴ ≤ 2ᵏ`. -/
def specDim (n s : ℕ) : ℕ := min n (Nat.clog 2 (16 * s ^ 4))

/-- The linear subspaces of `F₂ⁿ` of dimension exactly `d`. -/
def SubspOfDim (n d : ℕ) : Type :=
  {H : Submodule (ZMod 2) (V n) // Module.finrank (ZMod 2) H = d}

instance (n : ℕ) : Finite (Submodule (ZMod 2) (V n)) :=
  Finite.of_injective (fun p : Submodule (ZMod 2) (V n) => (p : Set (V n))) SetLike.coe_injective

noncomputable instance (n d : ℕ) : Fintype (SubspOfDim n d) := by
  unfold SubspOfDim; exact Fintype.ofFinite _

/-- For `d ≤ n` there is a `d`-dimensional subspace: the span of the first `d` unit vectors. -/
theorem subspOfDim_nonempty {n d : ℕ} (h : d ≤ n) : Nonempty (SubspOfDim n d) := by
  have hli : LinearIndependent (ZMod 2) ((Pi.basisFun (ZMod 2) (Fin n)) ∘ Fin.castLE h) :=
    (Pi.basisFun (ZMod 2) (Fin n)).linearIndependent.comp _ (Fin.castLE_injective h)
  exact ⟨⟨Submodule.span (ZMod 2) (Set.range ((Pi.basisFun (ZMod 2) (Fin n)) ∘ Fin.castLE h)),
    by rw [finrank_span_eq_card hli, Fintype.card_fin]⟩⟩

instance (n s : ℕ) : Nonempty (SubspOfDim n (specDim n s)) :=
  subspOfDim_nonempty (min_le_left _ _)

/-- The random seed of `SpectrumTest` (Algorithm 1, step 1): a `d`-dimensional subspace `H`,
`d = specDim n s`, and the two shifts `a, r ∈ F₂ⁿ`. -/
abbrev SpecSeed (n s : ℕ) : Type := SubspOfDim n (specDim n s) × V n × V n

open Classical in
/-- The points of a subspace `H`, listed once each in a fixed order. -/
noncomputable def pointList {n : ℕ} (H : Submodule (ZMod 2) (V n)) : List (V n) :=
  (Finset.univ.filter fun x : V n => x ∈ H).toList

/-- Algorithm 1, step 2, p.8: the query list of one run on seed `(H, a, r)`: the points of the four
cosets `H`, `a + H`, `r + H`, `a + r + H`, each enumerated in the fixed order of `H`
(`4 · 2^d` queries, repetitions charged). -/
noncomputable def specQueries {n s : ℕ} (σ : SpecSeed n s) : List (V n) :=
  (pointList σ.1.1).map (fun h => (0 : V n) + h) ++ (pointList σ.1.1).map (fun h => σ.2.1 + h) ++
    (pointList σ.1.1).map (fun h => σ.2.2 + h) ++
    (pointList σ.1.1).map (fun h => σ.2.1 + σ.2.2 + h)

open Classical in
/-- Read a Boolean function off a query list and its answer list: at a queried point, the answer
at its first occurrence; at any other point the fixed default bit `false`. -/
noncomputable def decodeFrom {n : ℕ} (qs : List (V n)) (ans : List Bool) : BoolFn n :=
  fun x => ans.getD (qs.idxOf x) false

/-- The uniform law on a nonempty finite seed type, as a measure on the discrete σ-algebra. -/
noncomputable def uniformLaw (S : Type) [Fintype S] [Nonempty S] :
    @MeasureTheory.Measure S ⊤ :=
  @PMF.toMeasure S ⊤ (PMF.uniformOfFintype S)

open Classical in
/-- **SpectrumTest** (Algorithm 1, p.8) as a nonadaptive query algorithm on `F₂ⁿ`, for the sparsity
parameter `s` and a fixed rule `Wsel` choosing the complement `W = Wsel H` of `H^⊥`.

* Seed: `(H, a, r)` uniform on `SpecSeed n s` — `H` uniform among the `d`-dimensional subspaces,
  `d = min{n, ⌈log₂(16s⁴)⌉}`, and `a, r` uniform on `F₂ⁿ`, all independent.
* Queries: `specQueries`, the four cosets `H, a+H, r+H, a+r+H`, fixed by the seed alone.
* Output: `1` (accept) if the four checks of steps 3–6 (`checksPass`) hold for the function decoded
  from the answers, at shifts `a, r`; `0` (reject) otherwise. The output reads only the seed and
  the answers. -/
noncomputable def spectrumTest (n s : ℕ)
    (Wsel : Submodule (ZMod 2) (V n) → Submodule (ZMod 2) (V n)) :
    NonadaptiveAlgorithm (V n) where
  Seed := SpecSeed n s
  seedMeasurable := ⊤
  law := uniformLaw (SpecSeed n s)
  probability := @PMF.toMeasure.isProbabilityMeasure _ ⊤ _
  queries := specQueries
  queries_measurable := fun _ _ => trivial
  output := fun σ ans =>
    if checksPass s σ.1.1 (Wsel σ.1.1) (decodeFrom (specQueries σ) ans) σ.2.1 σ.2.2 then 1 else 0
  output_measurable := fun _ _ _ => trivial

end FourierSparseTesting1656.Uniform.Supplement


