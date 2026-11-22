-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
-- name    : Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:18:37.84405+00:00
-- url     : https://prove2.me/theorems/3c93372b-881c-43bf-8789-3d116ef72373
-- title:
--   Fock Blocks
-- statement:
--   Definitions and structural lemmas for Fock Blocks, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM.FockB
open MvPolynomial Finset
section Ops
variable {k σ : Type} [Field k]
def atoms (S : Set σ) : Set (Module.End k (MvPolynomial σ k)) :=
  {T | ∃ u ∈ S, T = LinearMap.mulLeft k (X u) ∨ T = (pderiv u).toLinearMap}
noncomputable def Ops (S : Set σ) : Subalgebra k (Module.End k (MvPolynomial σ k)) :=
  Algebra.adjoin k (atoms S)
end Ops
end Formalism.GM.FockB
namespace Formalism.GM.FockB
open MvPolynomial Finset
section Pair
variable {k σ : Type} [Field k] {r : ℕ}
def V (w e : Fin r → σ) (zv sv : σ) : Set σ := Set.range w ∪ Set.range e ∪ {zv, sv}
noncomputable def Ehp (w e : Fin r → σ) (zv sv : σ) : MvPolynomial σ k :=
  X zv * X sv + ∑ c, X (w c) * X (e c)
noncomputable def Pop (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ) : Module.End k (MvPolynomial σ k) :=
  ∑ l ∈ range (o + 1), (((-1 : k) ^ l) / (((l.factorial : k) ^ 2) * ((o + n + r + z - 1).choose l : k))) •
    (M.tieEh w e zv sv ^ l * Formalism.GM.tieF w e ^ l * LinearMap.mulLeft k (X zv ^ z))
def Good (w e : Fin r → σ) (zv sv : σ) (o n : ℕ) (y : MvPolynomial σ k) : Prop :=
  ProjS.eulL w y = (o : k) • y ∧ ProjS.eulL e y = (n : k) • y ∧ pderiv zv y = 0 ∧ pderiv sv y = 0
variable {w e : Fin r → σ} {zv sv : σ}
end Pair
end Formalism.GM.FockB
namespace Formalism.GM.FockB
open MvPolynomial Finset
section Chain
variable {k σ α : Type} [Field k] {r : ℕ} (w e : α → Fin r → σ) (zv sv : α → σ) (z : α → ℕ)
def Va (a : α) : Set σ := V (w a) (e a) (zv a) (sv a)
def VL (L : List α) : Set σ := {v | ∃ b ∈ L, v ∈ Va w e zv sv b}
noncomputable def chainP (o n : α → ℕ) (L : List α) (y : MvPolynomial σ k) : MvPolynomial σ k :=
  L.foldr (fun a acc => M.tieP (w a) (e a) (zv a) (sv a) (o a) (n a) (z a) acc) y
noncomputable def chainE (j : α → ℕ) (L : List α) : MvPolynomial σ k :=
  (L.map fun a => Ehp (w a) (e a) (zv a) (sv a) ^ j a).prod
noncomputable def chainPhi (o n : α → ℕ) (L : List α) : MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  L.foldr (fun a acc => Formalism.GM.tiePhi (w a) (e a) (o a) (n a) (z a) ∘ₗ acc) LinearMap.id
noncomputable def cst (o n j : α → ℕ) (L : List α) : k :=
  (L.map fun a => ((j a).factorial : k) ^ 2 * (((o a + n a + r + z a + 1 + j a - 1).choose (j a) : ℕ) : k) *
    ((z a).factorial : k)).prod
variable {w e zv sv z}
end Chain
end Formalism.GM.FockB
namespace Formalism.GM.FockB
open MvPolynomial Finset Formalism.GM.M
section Block
variable {N r : ℕ} (D : BlockData N)
def wA : Option (Fin D.T.t) → Fin r → BVar N r D.T.t :=
  fun a c => a.elim (Sum.inl (Fin.castSucc D.uPos, c)) (fun i => Sum.inl (finPos N (D.T.pos i), c))
def eA : Option (Fin D.T.t) → Fin r → BVar N r D.T.t :=
  fun a c => a.elim (xiVar N r D.T.t c) (fun i => Sum.inl (finPos N (D.T.pos i + 1), c))
def zA : Option (Fin D.T.t) → BVar N r D.T.t :=
  fun a => a.elim (scalZ N r D.T.t (Fin.last D.T.t)) (fun i => scalZ N r D.T.t (Fin.castSucc i))
def sA : Option (Fin D.T.t) → BVar N r D.T.t :=
  fun a => a.elim (scalS N r D.T.t (Fin.last D.T.t)) (fun i => scalS N r D.T.t (Fin.castSucc i))
def zzA : Option (Fin D.T.t) → ℕ := fun a => a.elim D.zPlus D.T.z
def oA (j : Fin D.T.t → ℕ) (jp : ℕ) : Option (Fin D.T.t) → ℕ :=
  fun a => a.elim (D.LL.deg D.uPos - jp) (fun i => (D.lettersAt j jp).deg (D.letterAt (D.T.pos i)))
def nA (j : Fin D.T.t → ℕ) (jp : ℕ) : Option (Fin D.T.t) → ℕ :=
  fun a => a.elim (D.B - jp) (fun i => (D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1)))
def jA (j : Fin D.T.t → ℕ) (jp : ℕ) : Option (Fin D.T.t) → ℕ := fun a => a.elim jp j
def LA : List (Option (Fin D.T.t)) := none :: (List.finRange D.T.t).map some
variable (p : ℕ) [Fact p.Prime]
variable {D}
end Block
end Formalism.GM.FockB
namespace Formalism.GM.FockB
open MvPolynomial Finset Formalism.GM.M
section Block2
variable {N r : ℕ} {D : BlockData N}
end Block2
end Formalism.GM.FockB
namespace Formalism.GM.FockB
open MvPolynomial Finset Formalism.GM.M
section Block3
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable {D : BlockData N}
end Block3
end Formalism.GM.FockB
namespace Formalism.GM.FockB
open MvPolynomial Finset Formalism.GM.M
end Formalism.GM.FockB
namespace Formalism.GM
end Formalism.GM


