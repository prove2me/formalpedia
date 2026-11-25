-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KerPLeOfPlace
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KerPLeOfPlace
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T14:03:55.294227+00:00
-- url     : https://prove2.me/theorems/129db532-588e-5666-87f0-2ddad6feeb2b
-- title:
--   Ker PLe Of Place
-- statement:
--   Definitions and structural lemmas for Ker PLe Of Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/KerPLeOfPlace.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
section Kernel
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
noncomputable def chiImg (j₀ : Fin (N + 1)) (x : Fin N → Ω) (p : TVar D N) :
    MvPolynomial (Fin (D + 1) × Fin N) Ω :=
  Fin.succAboveCases (α := fun _ => MvPolynomial (Fin (D + 1) × Fin N) Ω) j₀
    (-∑ k, X (p.1, k) * C (x k)) (fun k => X (p.1, k)) p.2
noncomputable def chiP (j₀ : Fin (N + 1)) (x : Fin N → Ω) :
    MvPolynomial (TVar D N) K →ₐ[K] MvPolynomial (Fin (D + 1) × Fin N) Ω :=
  aeval (chiImg j₀ x)
noncomputable def kerP (j₀ : Fin (N + 1)) (x : Fin N → Ω) : Ideal (MvPolynomial (TVar D N) K) :=
  RingHom.ker (chiP (K := K) (D := D) j₀ x).toRingHom
noncomputable def psiS : MvPolynomial (Fin (D + 1) × Fin N) Ω →+* OmS Ω D N :=
  (algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N)).comp
    (rename (R := Ω) (Sum.inr : Fin (D + 1) × Fin N → SVar D N)).toRingHom
end Kernel
end ReciprocityTheory.ChartRestriction.G.T0
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
namespace Data
variable (d : Data K ι Ω WT A)
end Data
end ReciprocityTheory.ChartRestriction.G.T0


