-- Prove2me | Definitions.Def_ModularCurve_ChartSemicontinuity
-- name    : ModularCurve_ChartSemicontinuity
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/486a51c1-4af7-57f2-afe6-f8ddb8c650eb
-- title:
--   Charts, coordinates and semicontinuity on the mod-q fibre
-- statement:
--   Throughout, $q$ is a prime, $A$ a valuation subring of $\overline{\mathbb Q}$ with a ring homomorphism $red : A \to k$ into a field $k$ of characteristic $q$, $N$ a level, and the modular polynomial data, Kronecker congruence and integrality hypotheses for `heckeAlphaBar`, `heckeBetaBar` are fixed; $P$ is a place specialization and $R$ a prolongation tuple over $P$. Here $\overline{F}_M$ denotes the $\overline{\mathbb Q}$-base change of the level-$M$ modular function field and $F_k = k(j,j_N)$ inside $\mathrm{LaurentSeries}\,k$.
--
--   `ReducesDivisors P` asserts: for every $f \in \overline{F}_N$ whose Laurent series lies in `CharPReduction.modularLocalized` for $A$ and $red$, whose image $\bar f$ under `modularRedLocHom` lies in $F_k$ and is non-zero, and every divisor $D$ with $D(V)=\operatorname{ord}_V f$, the push-forward of $D$ along `P.sp` equals the divisor of $\bar f$ at every place $v$ of $F_k$. `fibreReduction` names that reduction $\bar f$ as an element of $F_k$. `HasCoordinates P` asserts that over every place $v$ there is such a $T$ with $\bar T-c$ a uniformiser at $v$ for some $c \in k$, and with $T$ taking, at every place $u'$ of $\overline{F}_N$ with $P.\mathrm{sp}\,u'=v$, a value $a \in A$ such that $\operatorname{ord}_{u'}(T-a)>0$ and $\operatorname{ord}_v(\bar T-red\,a)>0$.
--
--   `LocalSemicontinuity R` is a one-sided form of the divisor laws: for $f \in \overline{F}_{Nq}$ integral for both prolongations with non-zero residues, $D$ its divisor, and $v$ not fixed by the square of `frobOnPlacesGeomLevel`, if $D\ge 0$ at all `IsStrictFst` places reducing to $v$ then $\mathrm{mapDomain}\ P.\mathrm{reduceFst}\ (P.\mathrm{fstDiv}\ D)$ at $v$ is at most $\operatorname{ord}_v$ of the first residue of $f$; symmetrically for the second component.
--
--   `chartClosure S` is $\mathrm{Subring.closure}\,S$, and `chartLocalSetFst R v S` the set of $f$ with $fu=g$ for some $g,u$ in that closure, $u$ being $R_1$-integral with first residue not taking the value $0$ at $v$. `ChartEtaleAt R v S` asks for $z \in S$ and a monic $m$ of degree $q+1$ over $\overline{F}_N$ such that: $z$ is $R_2$-integral with a non-zero Laurent coefficient in degree prime to $q$; adjoining the range of `heckeAlphaBar` together with $z$ gives all of $\overline{F}_{Nq}$; $z$ is a root of $m$ pushed along `heckeAlphaBar`, the images of the coefficients of $m$ lie in $\mathrm{Subring.closure}\,S$, and whenever the derivative of the pushed $m$ evaluated at $z$ is $R_1$-integral, its first residue does not take the value $0$ at $v$. `IsChartAt R v S` is a structure bundling: $R_1$-integrality of $S$ and regularity at $v$ of the first residues; membership in $S$ of the four functions $\alpha(\bar j),\alpha(\bar j_N),\beta(\bar j),\beta(\bar j_N)$ when $v$ is an affine geometric place and of their inverses otherwise; membership of the constants from $A$; the condition that any $\alpha(\varphi)$ which is $R_1$-integral and integral at all characteristic-zero places over $v$ is a quotient $s/e$ with $s,e \in S$ and $e$ non-vanishing at $v$; a value law matching $W$-values in $A$ with $v$-values of first residues at `IsStrictFst` places over $v$; separation of `IsStrictSnd` places over $v$ by a zero of some $S$-element non-vanishing at $v$; the étaleness condition; the dichotomy that every place reducing to $v$ is `IsStrictFst` or `IsStrictSnd`; and regularity of $S$ at all places reducing to $v$. `HasCharts R` asserts existence of such an $S$ at every $v$ not fixed by the square of `frobOnPlacesGeomLevel`.
--
--   **Relation to Mathlib.** The notions are the project's own: places as valuation subrings, divisors, regular prolongations and the modular function fields come from its `AlgebraicCurve` and `ModularCurve` developments. Mathlib supplies only the ambient constructions used, such as `Subring.closure`, `Finsupp.mapDomain`, `IntermediateField.adjoin` and `Polynomial.derivative`.
--
--   **Where it is used.** These predicates axiomatise what is needed of a local presentation of the characteristic-$q$ fibre of the level-$Nq$ modular curve as two copies of the level-$N$ curve, matched through `heckeAlphaBar`/`heckeBetaBar` and the Frobenius on places, and are used together with the divisor, cusp and split laws of a prolongation tuple to compute specialisations of divisor classes and the component group. That analysis of the fibre at $q$ underlies the level-lowering step of the route to Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_ChartSemicontinuity.lean

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_FibreModel
import Mathlib.Algebra.Polynomial.Derivative

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

namespace ModularCurve.PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

def ReducesDivisors (P : PlaceSpecialization A q N data hKr k red hα hβ) : Prop :=
  ∀ (f : modularFunctionFieldBar N)
    (hf : (f : LaurentSeries
      (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red)
    (hmem : CharPReduction.modularRedLocHom N A.toSubring red ⟨f, hf⟩ ∈ modularFunctionFieldC k N),
    CharPReduction.modularRedLocHom N A.toSubring red ⟨f, hf⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ V, D V = V.ord f) →
      ∀ v : Place k (modularFunctionFieldC k N),
        Finsupp.mapDomain P.sp D v =
          v.ord (⟨CharPReduction.modularRedLocHom N A.toSubring red ⟨f, hf⟩,
            hmem⟩ : modularFunctionFieldC k N)

def LocalSemicontinuity : Prop :=
  (∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ W, D W = W.ord f) →
      ∀ v : Place k (modularFunctionFieldC k N),
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v →
        (∀ W, P.IsStrictFst W → P.reduceFst W = v → 0 ≤ D W) →
        Finsupp.mapDomain P.reduceFst (P.fstDiv D) v ≤ v.ord (R.residue₁ ⟨f, h₁⟩)) ∧
  (∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ W, D W = W.ord f) →
      ∀ u : Place k (modularFunctionFieldC k N),
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr u) ≠ u →
        (∀ W, P.IsStrictSnd W → P.reduceSnd W = u → 0 ≤ D W) →
        Finsupp.mapDomain P.reduceSnd (P.sndDiv D) u ≤ u.ord (R.residue₂ ⟨f, h₂⟩))

noncomputable def fibreReduction (f : modularFunctionFieldBar N)
    (hf : (f : LaurentSeries
      (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red)
    (hmem : CharPReduction.modularRedLocHom N A.toSubring red ⟨f, hf⟩ ∈ modularFunctionFieldC k N) :
    modularFunctionFieldC k N :=
  ⟨CharPReduction.modularRedLocHom N A.toSubring red ⟨f, hf⟩, hmem⟩

omit R in

noncomputable def chartClosure (S : Set (modularFunctionFieldBar (N * q))) :
    Subring (modularFunctionFieldBar (N * q)) :=
  Subring.closure S

def chartLocalSetFst (v : Place k (modularFunctionFieldC k N))
    (S : Set (modularFunctionFieldBar (N * q))) : Set (modularFunctionFieldBar (N * q)) :=
  {f | ∃ (g u : modularFunctionFieldBar (N * q)) (_ : g ∈ chartClosure S) (_ : u ∈ chartClosure S)
      (hu₁ : u ∈ R.R₁.integers),
      ¬ v.HasValue (R.residue₁ ⟨u, hu₁⟩) (0 : k) ∧ f * u = g}

def ChartEtaleAt (v : Place k (modularFunctionFieldC k N))
    (S : Set (modularFunctionFieldBar (N * q))) : Prop :=
  ∃ (z : modularFunctionFieldBar (N * q)) (m : Polynomial (modularFunctionFieldBar N)),
    z ∈ S ∧
    (∃ hz₂ : z ∈ R.R₂.integers, ∃ n : ℤ, ¬ (q : ℤ) ∣ n ∧
      ((R.residue₂ ⟨z, hz₂⟩ : modularFunctionFieldC k N) : LaurentSeries k).coeff n ≠ 0) ∧
    IntermediateField.adjoin (AlgebraicClosure ℚ)
      (Set.range (heckeAlphaBar (AlgebraicClosure ℚ) N q) ∪ {z}) = ⊤ ∧
    m.Monic ∧ m.natDegree = q + 1 ∧
    (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom).eval z = 0 ∧
    (∀ i : ℕ, heckeAlphaBar (AlgebraicClosure ℚ) N q (m.coeff i) ∈ Subring.closure S) ∧
    ∀ h : (Polynomial.derivative (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom)).eval z
        ∈ R.R₁.integers,
      ¬ v.HasValue (R.residue₁ ⟨_, h⟩) (0 : k)

structure IsChartAt (v : Place k (modularFunctionFieldC k N))
    (S : Set (modularFunctionFieldBar (N * q))) : Prop where
  integral : ∀ s ∈ S, s ∈ R.R₁.integers
  regular : ∀ (s : modularFunctionFieldBar (N * q)) (hs : s ∈ S),
    (R.residue₁ ⟨s, integral s hs⟩ : modularFunctionFieldC k N) ∈ v.toValuationSubring
  gens_affine : IsAffineGeomPlace k N v →
    heckeAlphaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N) ∈ S ∧ heckeAlphaBar
      (AlgebraicClosure ℚ) N q (CharPModel.jNBar N) ∈ S ∧
    heckeBetaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N) ∈ S ∧ heckeBetaBar
      (AlgebraicClosure ℚ) N q (CharPModel.jNBar N) ∈ S
  gens_cusp : ¬ IsAffineGeomPlace k N v →
    heckeAlphaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N)⁻¹ ∈ S ∧ heckeAlphaBar
      (AlgebraicClosure ℚ) N q (CharPModel.jNBar N)⁻¹ ∈ S ∧
    heckeBetaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N)⁻¹ ∈ S ∧ heckeBetaBar
      (AlgebraicClosure ℚ) N q (CharPModel.jNBar N)⁻¹ ∈ S
  const_mem : ∀ a : A,
    algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ S
  nIncl : ∀ φ : modularFunctionFieldBar N,
    heckeAlphaBar (AlgebraicClosure ℚ) N q φ ∈ R.R₁.integers →
    (∀ u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.sp u₀ = v →
      φ ∈ u₀.toValuationSubring) →
    ∃ (s : modularFunctionFieldBar (N * q)) (_ : s ∈ S) (e : modularFunctionFieldBar (N * q))
      (he : e ∈ S),
      ¬ v.HasValue (R.residue₁ ⟨e, integral e he⟩) (0 : k) ∧
        heckeAlphaBar (AlgebraicClosure ℚ) N q φ * e = s
  valueLaw : ∀ (s : modularFunctionFieldBar (N * q)) (hs : s ∈ S)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
    P.IsStrictFst W → P.reduceFst W = v →
      ∃ a : A, W.HasValue s (a : AlgebraicClosure ℚ) ∧ v.HasValue (R.residue₁ ⟨s, integral s hs⟩)
        (red a)
  separates : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
    P.IsStrictSnd W → P.reduceFst W = v →
      ∃ (u : modularFunctionFieldBar (N * q)) (hu : u ∈ S),
        ¬ v.HasValue (R.residue₁ ⟨u, integral u hu⟩) (0 : k) ∧ 0 < W.ord u
  etale : ChartEtaleAt R v S
  dichotomy : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
    P.reduceFst W = v → P.IsStrictFst W ∨ P.IsStrictSnd W
  regularOver : ∀ s ∈ S, ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
    P.reduceFst W = v → s ∈ W.toValuationSubring

def HasCharts : Prop :=
  ∀ v : Place k (modularFunctionFieldC k N),
    frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v →
    ∃ S : Set (modularFunctionFieldBar (N * q)), IsChartAt R v S

def HasCoordinates (P : PlaceSpecialization A q N data hKr k red hα hβ) : Prop :=
  ∀ v : Place k (modularFunctionFieldC k N),
    ∃ (T : modularFunctionFieldBar N)
      (hT : (T : LaurentSeries
        (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red)
      (hmem : CharPReduction.modularRedLocHom N A.toSubring red ⟨T,
        hT⟩ ∈ modularFunctionFieldC k N),
      (∃ c : k, v.ord (fibreReduction T hT hmem - algebraMap k (modularFunctionFieldC k N) c) = 1) ∧
      ∀ u' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.sp u' = v →
        ∃ a : A, 0 < u'.ord (T - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
          (a : AlgebraicClosure ℚ)) ∧
          0 < v.ord (fibreReduction T hT hmem - algebraMap k (modularFunctionFieldC k N) (red a))

end ModularCurve.PlaceSpecialization


