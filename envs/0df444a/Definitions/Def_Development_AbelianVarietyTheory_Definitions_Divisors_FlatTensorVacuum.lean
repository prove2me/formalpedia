-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:46.574844+00:00
-- url     : https://prove2.me/theorems/163d0028-afe9-4335-863a-5e8c384e0215
-- title:
--   Flat Tensor Vacuum
-- statement:
--   Definitions and structural lemmas for Flat Tensor Vacuum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FlatTensorVacuum.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Theorems.Thm_GlobalTheory_RootEx_Model_conj_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
namespace GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
section Vertex
variable (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (c : ℕ)
def symN : Subgroup (GL (n ⊕ Fin c) k) := N k n c ((c + 1) / 2) ⊔ N k n c (c / 2 + 1)
def symR : Subgroup (GL (n ⊕ Fin c) k) := (embX c).range ⊔ symN k n c
variable {k n c}
theorem symN_conj {u : GL (n ⊕ Fin c) k} (hu : u ∈ symN k n c) (g : GL n k) :
    (embX c g)⁻¹ * u * embX c g ∈ symN k n c := by
  have h : symN k n c ≤ (symN k n c).comap (MulAut.conj (embX c g)⁻¹).toMonoidHom :=
    sup_le (fun v hv => Subgroup.mem_sup_left (by simpa using RootEx.Model.conj_mem hv g))
      fun v hv => Subgroup.mem_sup_right (by simpa using RootEx.Model.conj_mem hv g)
  simpa using h hu
def symPr (C : Subgroup (GL (n ⊕ Fin c) k)) : Subgroup (GL n k) where
  carrier := {g | ∃ u ∈ symN k n c, u * embX c g ∈ C}
  one_mem' := ⟨1, one_mem _, by simp⟩
  mul_mem' := by
    rintro g g' ⟨u, hu, h⟩ ⟨u', hu', h'⟩
    refine ⟨u * ((embX c g⁻¹)⁻¹ * u' * embX c g⁻¹), mul_mem hu (symN_conj hu' g⁻¹), ?_⟩
    convert C.mul_mem h h' using 1
    simp [mul_assoc]
  inv_mem' := by
    rintro g ⟨u, hu, h⟩
    refine ⟨(embX c g)⁻¹ * u⁻¹ * embX c g, symN_conj (inv_mem hu) g, ?_⟩
    convert C.inv_mem h using 1
    simp [mul_assoc]
variable {n' : Type*} [Fintype n'] [DecidableEq n']
def Kept : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → Prop
  | (Sum.inl _, Sum.inr i) => Even c ∧ i.val = c / 2
  | (Sum.inr l, Sum.inl _) => Odd c ∧ l.val = c / 2
  | _ => False
variable (n n' c) in

abbrev StepVar : Type _ := {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (c / 2 + 1) rs ∨ Kept rs}
open Classical in

def stepPt (x₀ : Matrix n n' k) (e : StepVar n c n' → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  basePt c x₀ + Matrix.of fun r s => if h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s) then e ⟨(r, s), h⟩ else 0
open Classical in

def keptPt (w : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Kept rs} → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  Matrix.of fun r s => if h : Kept (r, s) then w ⟨(r, s), h⟩ else 0
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def flatStep [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k)
    (w : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Kept rs} → k) : ℂ :=
  opE ψ ν (c / 2 + 1) (fun x => Φ (x + keptPt w)) x₀
def invVol (C : Subgroup (GL (n ⊕ Fin c) k)) : ℚ :=
  (C.relIndex (symN k n c ⊓ KO k _) : ℚ) / (KO k _).relIndex (symN k n c ⊓ C)
end Vertex
variable {k : Type*} [Field k] (G : Grid k)
def topRank (j : ℕ) : ℕ := G.r + 1 + G.m * (G.s - 1) + j * (G.t + 1)
variable {G} in

theorem topRank_add (hs : 1 ≤ G.s) (j : ℕ) : topRank G j + G.m = G.rank (G.m, j) + j + 1 := by
  obtain ⟨s, h⟩ := Nat.exists_eq_add_of_le' hs
  simp only [topRank, Grid.rank, h, Nat.add_sub_cancel]; ring
def frame {a c b : ℕ} (h : a + c = b) : Fin a ⊕ Fin c ≃ Fin b := finSumFinEquiv.trans (finCongr h)
def frameGL {a c b : ℕ} (h : a + c = b) : GL (Fin b) k ≃* GL (Fin a ⊕ Fin c) k :=
  Units.mapEquiv (Matrix.reindexAlgEquiv k k (frame h).symm).toMulEquiv
abbrev ColArgs : Type _ := ∀ j : ℕ, Matrix (Fin (topRank G (j + 1))) (Fin (topRank G j)) k
abbrev RowArgs : Type _ := ∀ i : ℕ, Matrix (Fin (G.rank (i, G.m))) (Fin (G.rank (i + 1, G.m))) k
abbrev Vars : Type _ :=
  ∀ j : Fin (G.m - 1), StepVar (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j)) → k
def topLast (j : ℕ) : Fin (topRank G j) := ⟨topRank G j - 1, by unfold topRank; omega⟩
variable {G}
def colVar (x : ColArgs G) (e : Vars G) (j : Fin (G.m - 1)) (r : Fin (topRank G (j + 1))) : k :=
  stepPt (x j) (e j) (.inl r) (.inr ⟨(G.m - 2 - j) / 2, by omega⟩)
def rowVar (x : ColArgs G) (e : Vars G) (j : ℕ) (s : Fin (topRank G j)) : k :=
  if h : j < G.m - 1 then ∑ l : Fin (G.m - 2 - j),
    if l.val = (G.m - 2 - j) / 2 then stepPt (x j) (e ⟨j, h⟩) (.inr l) (.inl s) else 0
  else x j (topLast G (j + 1)) s
def phase (x : ColArgs G) (e : Vars G) : k :=
  ∑ j : Fin (G.m - 1), (ch (stepPt (x j) (e j)) +
    if Even (G.m - 2 - j) then ∑ r, rowVar x e (j + 1) r * colVar x e j r else 0)
variable (hs : 1 ≤ G.s)
def downMap (x : ColArgs G) (e : Vars G) (j : ℕ) : Matrix (Fin (G.rank (G.m, j + 1))) (Fin (G.rank (G.m, j))) k :=
  if h : j < G.m - 1 then
    (stepPt (c := G.m - 2 - j) (x j) (e ⟨j, h⟩)).reindex (frame (by have := topRank_add hs (j + 1); omega))
      (frame (by have := topRank_add hs j; omega))
  else if h' : j + 1 = G.m then
    (x j).submatrix (Fin.castLE (by have := topRank_add hs (j + 1); omega))
      (Fin.cast (by have := topRank_add hs j; omega))
  else 0
def fill (x : ColArgs G) (y : RowArgs G) (e : Vars G) : G.Args
  | .theta i j => if h : i = G.m then ((downMap hs x e j).submatrix (Fin.cast (by rw [h])) (Fin.cast (by rw [h])))ᵀ else 0
  | .ex i j => if h : j = G.m then ((y i).submatrix (Fin.cast (by rw [h])) (Fin.cast (by rw [h])))ᵀ else 0
def toFrame {j : ℕ} (hj : j < G.m) :
    GL (Fin (G.rank (G.m, j))) k ≃* GL (Fin (topRank G j) ⊕ Fin (G.m - 1 - j)) k :=
  frameGL (by have := topRank_add hs j; omega)
def rowR {j : ℕ} (hj : j < G.m) : Subgroup (GL (Fin (G.rank (G.m, j))) k) :=
  (symR k _ _).comap (toFrame hs hj).toMonoidHom
def conjLevel (J : G.Level) (g : G.VertexGroup) {j : ℕ} (hj : j < G.m) :
    Subgroup (GL (Fin (topRank G j) ⊕ Fin (G.m - 1 - j)) k) :=
  ((J (G.m, j)).map (MulAut.conj (g (G.m, j))).toMonoidHom).map (toFrame hs hj).toMonoidHom
abbrev Cosets (J : G.Level) : Type _ := ∀ i : Fin (G.m - 2),
  DoubleCoset.Quotient (rowR hs (j := i + 1) (by omega) : Set (GL (Fin (G.rank (G.m, i + 1))) k)) (J (G.m, i + 1))
structure Reps (J : G.Level) where

  base : GL (Fin (G.rank (G.m, 0))) k

  rep : ∀ i : Fin (G.m - 2), DoubleCoset.Quotient (rowR hs (j := i + 1) (by omega) :
    Set (GL (Fin (G.rank (G.m, i + 1))) k)) (J (G.m, i + 1)) → GL (Fin (G.rank (G.m, i + 1))) k
  mk_rep : ∀ i β, DoubleCoset.mk _ _ (rep i β) = β
def onColumn (h : ∀ j : ℕ, GL (Fin (G.rank (G.m, j))) k) : G.VertexGroup := fun X =>
  if hi : X.1 = G.m then (show (G.m, X.2) = X from hi ▸ rfl) ▸ h X.2 else 1
variable {hs}
def Reps.elt {J : G.Level} (ρ : Reps hs J) (β : Cosets hs J) : G.VertexGroup := onColumn fun
  | 0 => ρ.base
  | i + 1 => if h : i < G.m - 2 then ρ.rep ⟨i, h⟩ (β ⟨i, h⟩) else 1
variable (hs) in
open Classical in

def Reps.through (J : G.Level) (h : ∀ j : ℕ, GL (Fin (G.rank (G.m, j))) k) : Reps hs J where
  base := h 0
  rep i β := if DoubleCoset.mk _ _ (h (i + 1)) = β then h (i + 1) else β.out
  mk_rep i β := by
    split_ifs with H
    · exact H
    · exact DoubleCoset.out_eq' _ _ β
variable (G) in

def stair (ϖ : kˣ) (e j : ℕ) : GL (Fin (G.rank (G.m, j))) k := diagGL fun a => ϖ ^ (e * (a.val + 1 - topRank G j))
variable (G) in

structure UnfTerm where

  coef : ℚ

  datum : ColArgs G → RowArgs G → ℂ

  pr : ∀ j : ℕ, 0 < j → j < G.m → Subgroup (GL (Fin (topRank G j)) k)

  row : ∀ i : ℕ, Subgroup (GL (Fin (G.rank (i, G.m))) k)
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable (G) in

def charFactor (g : G.VertexGroup) : ℂˣ :=
  ((oppositePath G.m).map fun b => G.kappa b b.src (gdet (g b.src)) * (G.kappa b b.tgt (gdet (g b.tgt)))⁻¹).prod
variable (G) in

def moved (keep : Bool) (g : G.VertexGroup) (T : G.Args → ℂ) : G.Args → ℂ := fun z =>
  (if keep then (1 : ℂ) else (((charFactor G g)⁻¹ : ℂˣ) : ℂ)) * G.pathAct .one (oppositePath G.m) g T z
variable [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)
variable (hs) in

def flatIntegrand (S : G.Args → ℂ) (x : ColArgs G) (y : RowArgs G) (e : Vars G) : ℂ :=
  S (fill hs x y e) * (ψ (-phase x e) : ℂ)
open Classical in
variable (G) in

def varsVol : Measure (Vars G) := Measure.pi fun _ => Measure.pi fun _ => ν
variable (hs) in

def flatTensor (S : G.Args → ℂ) (x : ColArgs G) (y : RowArgs G) : ℂ :=
  ∫ e, flatIntegrand hs ψ S x y e ∂(varsVol G ν)
variable (hs) in

def FlatIntegrable (T : G.Args → ℂ) : Prop :=
  ∀ g x y, Integrable (flatIntegrand hs ψ (moved G true g T) x y) (varsVol G ν)
variable {J : G.Level} (keep : Bool) (ρ : Reps hs J) (T : G.Args → ℂ)
def unfTerm (β : Cosets hs J) : UnfTerm G where
  coef := ∏ i : Fin (G.m - 2), invVol (conjLevel hs J (ρ.elt β) (j := i + 1) (by omega))
  datum := flatTensor hs ψ ν (moved G keep (ρ.elt β) T)
  pr _ _ hj := symPr (conjLevel hs J (ρ.elt β) hj)
  row i := J (i, G.m)
def unfSupport : Set (Cosets hs J) := {β | (unfTerm ψ ν keep ρ T β).datum ≠ 0}
def unf (hfin : (unfSupport ψ ν keep ρ T).Finite) : Multiset (UnfTerm G) :=
  hfin.toFinset.val.map (unfTerm ψ ν keep ρ T)
variable (hs J) in

def stairTerm (ϖ : kˣ) (e : ℕ) : UnfTerm G :=
  unfTerm ψ ν false (Reps.through hs J (stair G ϖ e)) T fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))
variable (hs J) in

def OneCoset (ϖ : kˣ) (e : ℕ) : Prop :=
  ∀ β ∈ unfSupport ψ ν false (Reps.through hs J (stair G ϖ e)) T, ∀ i, β i = DoubleCoset.mk _ _ (stair G ϖ e (i + 1))
example : topRank (⟨2, 3, 1, 1, 1, 1, 1⟩ : Grid k) 2 = (⟨2, 3, 1, 1, 1, 1, 1⟩ : Grid k).rank (2, 2) + 1 := rfl
end GlobalTheory.FunObj


