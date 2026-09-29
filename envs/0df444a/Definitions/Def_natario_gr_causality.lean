-- Prove2me | Definitions.Def_natario_gr_causality
-- name    : natario_gr_causality
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T13:57:40.041021+00:00
-- url     : https://prove2.me/theorems/8120a415-404f-4321-b8d3-f4f4a510d7fb
-- title:
--   Causality, Cauchy hypersurfaces, spacelike slices and trapped surfaces
-- statement:
--   Inextendible causal curves, Cauchy hypersurfaces and global hyperbolicity; the chronological and causal futures of a set; spacelike hypersurfaces with their unit normal, second fundamental form, expansion, conjugate points and maximizing curves; compact two-surfaces inside a hypersurface with their two null normals, the associated null expansions, and the notion of a trapped surface.
-- source:
--   J. Natário, Mathematical Relativity, arXiv:2003.02855, Chapter 4 (Singularity theorems), §§4.3-4.6

import Definitions.Def_natario_gr_curves
import Definitions.Def_natario_gr_congruence

open scoped ContDiff

/-!
# Causality, Cauchy hypersurfaces, spacelike slices and trapped surfaces

Continuation of the coordinate framework for J. Natário, *Mathematical Relativity*
(arXiv:2003.02855), Chapters 3 and 4.
-/

namespace MathematicalRelativity

namespace Spacetime

variable (m : Spacetime)

/-- An inextendible future-pointing causal curve: one defined for every value of its
parameter which approaches no endpoint, in either direction.  (Every causal curve can be
reparameterized so that its parameter ranges over all of `ℝ`, so the content of the
definition is the absence of endpoints.) -/
def IsInextendibleCausalCurve (c : ℝ → Pt) : Prop :=
  m.IsCausalCurveOn c Set.univ ∧
    ¬ (∃ p : Pt, Filter.Tendsto c Filter.atTop (nhds p)) ∧
    ¬ (∃ p : Pt, Filter.Tendsto c Filter.atBot (nhds p))

/-- `S` is a Cauchy hypersurface: every inextendible causal curve meets it exactly once. -/
def IsCauchySurface (S : Set Pt) : Prop :=
  ∀ c : ℝ → Pt, m.IsInextendibleCausalCurve c → ∃! t : ℝ, c t ∈ S

/-- Global hyperbolicity: the spacetime admits a Cauchy hypersurface. -/
def GloballyHyperbolic : Prop := ∃ S : Set Pt, m.IsCauchySurface S

/-- The chronological future `I⁺(A)`: points reached from `A` by a future-pointing
timelike curve. -/
def chronFuture (A : Set Pt) : Set Pt :=
  {q : Pt | ∃ (c : ℝ → Pt) (t₁ : ℝ), 0 < t₁ ∧ m.IsTimelikeCurveOn c (Set.Icc 0 t₁) ∧
      c 0 ∈ A ∧ c t₁ = q}

/-- The causal future `J⁺(A)`: points reached from `A` by a future-pointing causal curve,
together with `A` itself. -/
def causalFuture (A : Set Pt) : Set Pt :=
  {q : Pt | q ∈ A ∨ ∃ (c : ℝ → Pt) (t₁ : ℝ), 0 < t₁ ∧ m.IsCausalCurveOn c (Set.Icc 0 t₁) ∧
      c 0 ∈ A ∧ c t₁ = q}

end Spacetime

/-- A smooth spacelike hypersurface, presented as the zero level set of a function `f`
with nowhere vanishing differential, together with its future-pointing unit normal field
`N` (Natário, §4.3). -/
structure Slice (m : Spacetime) where
  f : Pt → ℝ
  f_smooth : ContDiff ℝ ∞ f
  N : Pt → Pt
  N_smooth : ∀ a, ContDiff ℝ ∞ (fun x => N x a)
  N_unit : ∀ x, m.ip x (N x) (N x) = -1
  N_future : ∀ x, Spacetime.IsFuture (N x)
  N_normal : ∀ x, ∃ lam : ℝ, lam ≠ 0 ∧ ∀ a, pd f a x = lam * m.lower x (N x) a

namespace Slice

variable {m : Spacetime}

/-- The hypersurface as a subset of spacetime. -/
def carrier (S : Slice m) : Set Pt := {x : Pt | S.f x = 0}

/-- The second fundamental form `K_{μν} = ∇_ν N_μ` of the hypersurface. -/
noncomputable def K (S : Slice m) (u v : Fin 4) (x : Pt) : ℝ := m.covCov S.N v u x

/-- The expansion `θ = ∇_a N^a` of the congruence of future-pointing timelike geodesics
orthogonal to the hypersurface: the trace of its second fundamental form. -/
noncomputable def expansion (S : Slice m) (x : Pt) : ℝ := m.divergence S.N x

/-- The geodesic `c` leaves the hypersurface orthogonally at parameter `t₀`. -/
def OrthogonalAt (S : Slice m) (c : ℝ → Pt) (t₀ : ℝ) : Prop :=
  c t₀ ∈ S.carrier ∧ vel c t₀ = S.N (c t₀)

/-- `c t₁` is conjugate to the hypersurface `S` along the geodesic `c`, which leaves `S`
orthogonally at `t₀` (Natário, Def. 4.3.4). -/
def ConjugateToSlice (S : Slice m) (c : ℝ → Pt) (t₀ t₁ : ℝ) : Prop :=
  ∃ Y : ℝ → Pt, m.IsJacobiFieldOn c Y (Set.Icc t₀ t₁) ∧
    (∃ t ∈ Set.Icc t₀ t₁, Y t ≠ 0) ∧
    m.ip (c t₀) (S.N (c t₀)) (Y t₀) = 0 ∧
    (∀ a, m.covDAlong c Y t₀ a = ∑ b, m.covVec S.N a b (c t₀) * Y t₀ b) ∧
    Y t₁ = 0

/-- The timelike curve `c`, running from the hypersurface `S` at parameter `0` to its
endpoint at parameter `T`, maximizes proper time among all future-pointing timelike
curves from `S` to that same endpoint. -/
def MaximizesFromSlice (S : Slice m) (c : ℝ → Pt) (T : ℝ) : Prop :=
  ∀ (d : ℝ → Pt) (T' : ℝ), 0 < T' → m.IsTimelikeCurveOn d (Set.Icc 0 T') →
    d 0 ∈ S.carrier → d T' = c T → m.properTime d 0 T' ≤ m.properTime c 0 T

end Slice

/-- A compact two-dimensional surface inside the spacelike hypersurface `S`, presented as
the intersection of `S` with the zero level set of a function `h`, together with the unit
normal field `n` of the surface inside `S` (Natário, §4.6).  The defining data are only
required on an open neighbourhood `U` of the surface. -/
structure Surface (m : Spacetime) (S : Slice m) where
  U : Set Pt
  U_open : IsOpen U
  h : Pt → ℝ
  h_smooth : ContDiffOn ℝ ∞ h U
  n : Pt → Pt
  n_smooth : ∀ a, ContDiffOn ℝ ∞ (fun x => n x a) U
  n_unit : ∀ x ∈ U, m.ip x (n x) (n x) = 1
  n_orth : ∀ x ∈ U, m.ip x (n x) (S.N x) = 0
  n_normal : ∀ x ∈ U, ∃ lam : ℝ, lam ≠ 0 ∧ ∀ a, pd h a x = lam * m.lower x (n x) a
  subset : {x : Pt | S.f x = 0 ∧ h x = 0} ⊆ U
  compact : IsCompact {x : Pt | S.f x = 0 ∧ h x = 0}

namespace Spacetime

variable (m : Spacetime)

/-- The projector `P^{μν} = g^{μν} + (l^μ k^ν + k^μ l^ν)/2` onto the two-plane orthogonal
to a pair of future null normals `l`, `k` normalised by `⟪l, k⟫ = -2`. -/
noncomputable def nullProj (l k : Pt → Pt) (u v : Fin 4) (x : Pt) : ℝ :=
  m.ginv x u v + (1/2 : ℝ) * (l x u * k x v + k x u * l x v)

/-- The null expansion `θ = P^{μν} ∇_μ l_ν` of the null normal `l`, the complementary null
normal being `k` (Natário, §4.6). -/
noncomputable def nullExpansion (l k : Pt → Pt) (x : Pt) : ℝ :=
  ∑ u, ∑ v, m.nullProj l k u v x * m.covCov l u v x

end Spacetime

namespace Surface

variable {m : Spacetime} {S : Slice m}

/-- The surface as a subset of spacetime. -/
def carrier (Sig : Surface m S) : Set Pt := {x : Pt | S.f x = 0 ∧ Sig.h x = 0}

/-- The future null normal `l⁺ = N + n`. -/
def lplus (Sig : Surface m S) (x : Pt) : Pt := fun a => S.N x a + Sig.n x a

/-- The future null normal `l⁻ = N - n`. -/
def lminus (Sig : Surface m S) (x : Pt) : Pt := fun a => S.N x a - Sig.n x a

/-- The expansion `θ⁺` of the null geodesics with initial condition `N + n`. -/
noncomputable def thetaPlus (Sig : Surface m S) (x : Pt) : ℝ :=
  m.nullExpansion Sig.lplus Sig.lminus x

/-- The expansion `θ⁻` of the null geodesics with initial condition `N - n`. -/
noncomputable def thetaMinus (Sig : Surface m S) (x : Pt) : ℝ :=
  m.nullExpansion Sig.lminus Sig.lplus x

/-- A trapped surface: both null expansions are negative everywhere on the surface
(Natário, Def. 4.6.4). -/
def IsTrapped (Sig : Surface m S) : Prop :=
  ∀ x ∈ Sig.carrier, Sig.thetaPlus x < 0 ∧ Sig.thetaMinus x < 0

/-- The null geodesic `c` leaves the surface orthogonally at parameter `t₀`, with initial
velocity the null normal `l`. -/
def NormalNullGeodesicAt (Sig : Surface m S) (l : Pt → Pt) (c : ℝ → Pt) (t₀ : ℝ) : Prop :=
  c t₀ ∈ Sig.carrier ∧ vel c t₀ = l (c t₀)

/-- `c t₁` is conjugate to the surface along the null geodesic `c`, which leaves the
surface orthogonally at `t₀` in the direction of the null normal `l` (Natário, Def. 4.6.1,
in its Jacobi field formulation). -/
def ConjugateToSurface (Sig : Surface m S) (l : Pt → Pt) (c : ℝ → Pt) (t₀ t₁ : ℝ) : Prop :=
  ∃ Y : ℝ → Pt, m.IsJacobiFieldOn c Y (Set.Icc t₀ t₁) ∧
    (∃ t ∈ Set.Icc t₀ t₁, Y t ≠ 0) ∧
    m.ip (c t₀) (S.N (c t₀)) (Y t₀) = 0 ∧
    m.ip (c t₀) (Sig.n (c t₀)) (Y t₀) = 0 ∧
    (∀ a, m.covDAlong c Y t₀ a = ∑ b, m.covVec l a b (c t₀) * Y t₀ b) ∧
    Y t₁ = 0

end Surface

end MathematicalRelativity


