-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CPfSym
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_CPfSym
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:12.372673+00:00
-- url     : https://prove2.me/theorems/50956cba-59c5-4e39-bce1-fd1773b36e88
-- title:
--   CPf Sym
-- statement:
--   Definitions and structural lemmas for CPf Sym, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CPfSym.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LegendreSumSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace Sym
variable {k : Type} [CommRing k] {σ : Type}
def OrdGE (r : ℕ) (g : MvPowerSeries σ k) : Prop := ∀ e : σ →₀ ℕ, e.degree < r → coeff e g = 0
def op {d : ℕ} (a : Fin d → MvPowerSeries σ k) (cd : Fin d → σ) (g : MvPowerSeries σ k) : MvPowerSeries σ k :=
  ∑ j, a j * pderiv k (cd j) g
end Sym
namespace Sym
variable {k : Type} [CommRing k] {σ : Type}
structure GoodPair (D D₀ : MvPowerSeries σ k → MvPowerSeries σ k) : Prop where
  ord : ∀ r g, OrdGE (r + 1) g → OrdGE r (D g)
  ord₀ : ∀ r g, OrdGE (r + 1) g → OrdGE r (D₀ g)
  diff : ∀ r g, OrdGE (r + 1) g → OrdGE (r + 1) (D g - D₀ g)
  sub : ∀ f g, D (f - g) = D f - D g
end Sym
namespace Sym
variable {k : Type} [CommRing k]
end Sym
namespace Sym
variable {k : Type} [CommRing k]
end Sym
namespace Sym
variable {k : Type} [CommRing k]
end Sym
namespace Sym
variable {k : Type} [CommRing k]
end Sym
namespace Sym
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type} [CommRing k]
  [Algebra ℚ k] [Algebra R k]
end Sym
namespace Sym
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type} [CommRing k]
  [Algebra ℚ k] [Algebra R k]
end Sym
end Formalism.MainNotions.ModuliIntegralCharts.H1


