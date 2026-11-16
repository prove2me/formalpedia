-- Prove2me | Definitions.Def_QuantumSymmetryBreaking_CycleColoring_Supplement_HilbertLimit
-- name    : QuantumSymmetryBreaking_CycleColoring_Supplement_HilbertLimit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:06:06.086186+00:00
-- url     : https://prove2.me/theorems/c1721313-f18e-4ed6-9cb8-0c4db3f8f785
-- title:
--   Hilbert–Schmidt completion and bounded realization of the specified limit
-- statement:
--   Let G be the free product of s copies of the order-two group, with the exact published recursion V_n of equation (2). The two Hilbert spaces are H=ℓ²(G) and ℓ²(G×G). A bounded operator realizes a coefficient array X when its matrix entries on every pair of standard basis vectors equal X(g,h). The limit predicate is
--
--   $$\|V_n-V\|_F\longrightarrow 0.$$
--
--   The norm is extended nonnegative real, with no conversion that could replace infinity by zero. The standard ket, vacuum projection |e⟩⟨e|, signed colors (i,±), opposite color, and literal coefficients of P_{±i} are defined. Word evaluation applies the rightmost operator first; the empty product is identity. No default-valued limit or theorem conclusion is built into a structure. These definitions realize the published kernels as bounded operators through their full coefficient interface; the existence of the prescribed realization is part of Theorem B.1.
-- source:
--   Maxime Flin, Longcheng Li, Jukka Suomela, Quantum Advantage for Distributed Symmetry Breaking, STOC 2027 submission #863 (October 2026), §4.1 pp.12–14 (PDF 15–17), Appendix B pp.44–46 (PDF 47–49)

import Mathlib
import Definitions.Def_QuantumSymmetryBreaking_CycleColoring_InfiniteConstruction

set_option autoImplicit false
open scoped ENNReal Topology

/-! The actual Hilbert spaces and bounded-operator realization of Appendix B,
Flin–Li–Suomela, STOC 2027 #863, pp.12–14 and 44–46.
No limit is defaulted and no positivity property is part of a definition. -/
namespace QuantumSymmetryBreaking.CycleColoring.Supplement

/-- The source's H = ℓ²(G). -/
noncomputable abbrev GroupHilbert (s : ℕ) := lp (fun _ : G s => ℂ) 2

/-- Hilbert–Schmidt completion of finite coefficient arrays, ℓ²(G×G). -/
noncomputable abbrev KernelHilbert (s : ℕ) := lp (fun _ : G s × G s => ℂ) 2

/-- Standard unit basis vector |g⟩. -/
noncomputable def basisKet {s : ℕ} (g : G s) : GroupHilbert s :=
  by classical exact lp.single 2 g 1

/-- The coefficient interface of a genuine bounded operator. Coefficients on
all unit vectors uniquely determine a continuous map on ℓ²(G). -/
def RealizesKernel {s : ℕ} (X : Op s)
    (T : GroupHilbert s →L[ℂ] GroupHilbert s) : Prop :=
  ∀ g h, (T (basisKet h)) g = X (g,h)

/-- Hilbert–Schmidt convergence to V of the specified recursion (2).
ENNReal norms preserve infinity and are never converted with toReal. -/
def IsSpecifiedLimit {s : ℕ} (V : KernelHilbert s) : Prop :=
  Filter.Tendsto (fun n => opFrob (opV s n - fun p => V p)) Filter.atTop (𝓝 0)

/-- Identity kernel, used only to express the literal projection coefficients. -/
noncomputable def identityKernel (s : ℕ) : Op s := by
  classical
  exact fun p => if p.1 = p.2 then 1 else 0

/-- The signed color +i is (i,true), -i is (i,false). These are not group letters. -/
abbrev SignedColor (s : ℕ) := Fin s × Bool

/-- Exact coefficient array of P_{±i} from §4.1. -/
noncomputable def projectionKernel {s : ℕ} (a : SignedColor s) : Op s :=
  if a.2 then projPlusLeft a.1 (identityKernel s)
  else projMinusLeft a.1 (identityKernel s)

/-- Opposite signed color. -/
def opposite {s : ℕ} (a : SignedColor s) : SignedColor s := (a.1, !a.2)

/-- E = |e⟩⟨e|, as a bounded operator, with no infinite sum. -/
noncomputable def vacuumProjection (s : ℕ) : GroupHilbert s →L[ℂ] GroupHilbert s :=
  by
    classical
    exact (lp.singleContinuousLinearMap ℂ (fun _ : G s => ℂ) 2 1).comp
      (lp.evalCLM ℂ (fun _ : G s => ℂ) 2 1)

/-- Vacuum matrix element of an ordered finite product, including the empty
word (identity). List.foldr applies the rightmost operator first. -/
noncomputable def wordVacuum {s : ℕ}
    (T : SignedColor s → GroupHilbert s →L[ℂ] GroupHilbert s)
    (w : List (SignedColor s)) : ℂ :=
  (w.foldr (fun a x => T a x) (basisKet 1)) 1

end QuantumSymmetryBreaking.CycleColoring.Supplement


