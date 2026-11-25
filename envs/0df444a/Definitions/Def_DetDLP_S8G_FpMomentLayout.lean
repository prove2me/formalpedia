-- Prove2me | Definitions.Def_DetDLP_S8G_FpMomentLayout
-- name    : DetDLP_S8G_FpMomentLayout
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:27:54.756824+00:00
-- url     : https://prove2.me/theorems/6caa6f88-7aac-443e-aec2-9042287b7801
-- title:
--   Bit identification, repeated layouts, and witness types for prime-field moment queries
-- statement:
--   Identifying bit vertices adds their incident degrees and restricts satisfying assignments to those consistent on each identified class. A rectangular family of layouts tests each coordinate separately. For each of the four moment indices, erasing the arithmetic certificates is a bijection onto a finite type of the required cardinality.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2, Theorem 3.1 (pp. 11–13)

import Definitions.Def_DetDLP_S8G_FpMomentGraph
import Definitions.Def_DetDLP_S8G_FpMomentCert

set_option autoImplicit false
namespace DetDLP.S8G.FpMoment.Gluing

/-- Merge occurrences of a shared bus bit, leaving the complete gate-incidence lists unchanged. -/
def identify (A : w3_FactorLayout) {k : ℕ} (f : Fin A.nb → Fin k) (rep : Fin k → Fin A.nb)
    (hr : Function.RightInverse rep f) : w3_FactorLayout where
  ng := A.ng
  ne := A.ne
  nb := k
  gate := A.gate
  bit := f ∘ A.bit
  rep := A.rep ∘ rep
  rep_bit i := by simp only [Function.comp_apply,A.rep_bit,hr i]

variable {A : w3_FactorLayout} {k : ℕ} {f : Fin A.nb → Fin k} {rep : Fin k → Fin A.nb}
variable (hr : Function.RightInverse rep f)

theorem gates (g : Fin A.ng) :
    (w3_factorGraph (identify A f rep hr)).deg (Fin.castAdd k g) =
      (w3_factorGraph A).deg (Fin.castAdd A.nb g) :=
  (w3_gateDegree (identify A f rep hr) g).trans (w3_gateDegree A g).symm

private theorem bitCard (L : w3_FactorLayout) (b : Fin L.nb) :
    (w3_factorGraph L).deg (Fin.natAdd L.ng b) = Fintype.card {e : Fin L.ne // L.bit e = b} := by
  rw [Fintype.card_subtype, w3_bitDegree, ← List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _)]
  apply congrArg Finset.card
  ext e
  simp

/-- The number of incidences on a glued bit is the sum over its original copy vertices. -/
theorem sharedDegree (b : Fin k) :
    (w3_factorGraph (identify A f rep hr)).deg (Fin.natAdd A.ng b) =
      ∑ a : {i // f i = b}, (w3_factorGraph A).deg (Fin.natAdd A.ng a.val) := by
  apply (bitCard (identify A f rep hr) b).trans
  change Fintype.card {e : Fin A.ne // f (A.bit e) = b} = _
  simp_rw [bitCard A]
  rw [← Fintype.card_sigma]
  apply Fintype.card_congr
  exact {
    toFun := fun e => ⟨⟨A.bit e.val,e.property⟩,e.val,rfl⟩
    invFun := fun ⟨i,e,h⟩ => ⟨e, (congrArg f h).trans i.property⟩
    left_inv := fun _ => rfl
    right_inv := by
      rintro ⟨⟨i,hi⟩,e,he⟩
      change A.bit e = i at he
      subst i
      rfl }

theorem sharedBound (b : Fin k) (D t : ℕ)
    (hd : ∀ i : Fin A.nb, f i = b → (w3_factorGraph A).deg (Fin.natAdd A.ng i) ≤ D)
    (ht : Fintype.card {i // f i = b} ≤ t) :
    (w3_factorGraph (identify A f rep hr)).deg (Fin.natAdd A.ng b) ≤ t*D := by
  rw [sharedDegree hr b]
  calc _ ≤ ∑ _ : {i // f i = b}, D := Finset.sum_le_sum fun i _ => hd i.val i.property
       _ = _ := by simp
       _ ≤ t*D := Nat.mul_le_mul_right _ ht

/-- Projection to the old bits is bijective exactly on the assignments constant on each bus. -/
def consistent (test : w3_factorTest A) :
    {y : Fin k → Bool // ∀ g, test g (fun e => y (f (A.bit e.val))) = true} ≃
    {x : Fin A.nb → Bool // (∀ g, test g (fun e => x (A.bit e.val)) = true) ∧
      ∀ i, x i = x (rep (f i))} where
  toFun y := ⟨y.val ∘ f,y.property,fun i => congrArg y.val (hr (f i)).symm⟩
  invFun x := ⟨x.val ∘ rep,fun g => by simpa only [Function.comp_apply,← x.property.2] using x.property.1 g⟩
  left_inv y := Subtype.ext (funext fun b => congrArg y.val (hr b))
  right_inv x := Subtype.ext (funext fun i => (x.property.2 i).symm)

def graphEquiv (test : w3_factorTest A) :
    {y // (w3_factorGraph (identify A f rep hr)).Satisfies (w3_factorChecks _ test) y} ≃
    {x : Fin A.nb → Bool // (∀ g, test g (fun e => x (A.bit e.val)) = true) ∧
      ∀ i, x i = x (rep (f i))} :=
  (w3_factorEquiv (identify A f rep hr) test).trans (consistent hr test)

end DetDLP.S8G.FpMoment.Gluing

namespace DetDLP.S8G.FpMoment

/-- A rectangular array of identical layouts, indexed first by slot, then by local address. -/
def tileMap {m a b : ℕ} (f : Fin a → Fin b) (x : Fin (m*a)) : Fin (m*b) :=
  let ix : Fin m × Fin a := finProdFinEquiv.symm x
  finProdFinEquiv (ix.1, f ix.2)

@[simp] theorem tileMap_at {m a b : ℕ} (f : Fin a → Fin b) (i : Fin m) (e : Fin a) :
    tileMap f (finProdFinEquiv (i,e)) = finProdFinEquiv (i,f e) := by simp [tileMap]

def tiles (m : ℕ) (A : w3_FactorLayout) : w3_FactorLayout where
  ng := m*A.ng
  ne := m*A.ne
  nb := m*A.nb
  gate := tileMap A.gate
  bit := tileMap A.bit
  rep := tileMap A.rep
  rep_bit i := by
    obtain ⟨⟨u,v⟩,rfl⟩ := finProdFinEquiv.surjective i
    simp [A.rep_bit]

theorem tiles_gates {m : ℕ} {A : w3_FactorLayout} (h : Function.Surjective A.gate) :
    Function.Surjective (tiles m A).gate := by
  intro i
  obtain ⟨⟨u,v⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨e,rfl⟩ := h v
  exact ⟨finProdFinEquiv (u,e),tileMap_at ..⟩

/-- A global assignment read at a tile's bit vertices. -/
def atTile {m n : ℕ} (x : Fin (m*n) → Bool) (i : Fin m) (e : Fin n) := x (finProdFinEquiv (i,e))

def tileTests {m : ℕ} {A : w3_FactorLayout} (t : Fin m → w3_factorTest A) : w3_factorTest (tiles m A) :=
  fun g vals =>
    let u : Fin m × Fin A.ng := finProdFinEquiv.symm g
    t u.1 u.2 (fun e => vals ⟨finProdFinEquiv (u.1,e.1), by
      change tileMap A.gate _ = g
      rw [tileMap_at,e.2]; exact finProdFinEquiv.apply_symm_apply g⟩)

theorem tileTests_iff {m : ℕ} {A : w3_FactorLayout} (t : Fin m → w3_factorTest A)
    (x : Fin (m*A.nb) → Bool) :
    (∀ g, tileTests t g (fun e => x ((tiles m A).bit e.val)) = true) ↔
    ∀ i g, t i g (fun e => atTile x i (A.bit e.val)) = true := by
  let good (ig : Fin m × Fin A.ng) := t ig.1 ig.2 (fun e => atTile x ig.1 (A.bit e.val)) = true
  have hh (g : Fin (m*A.ng)) :
      tileTests t g (fun e => x ((tiles m A).bit e.val)) = true ↔ good (finProdFinEquiv.symm g) := by
    simp only [tileTests, tiles, good, atTile, tileMap_at]
  constructor
  · intro h i g
    change good (i,g)
    exact (finProdFinEquiv.symm_apply_apply (i,g)) ▸ ((hh _).mp (h (finProdFinEquiv (i,g))))
  · intro h g
    exact (hh _).mpr (h _ _)

variable (p m T : ℕ) [Fact p.Prime] (η : List Bool)

/-- The four semantic targets of a moment layout. -/
def Target : Fin 4 → Type
  | 0 => Mass p (m+1) η
  | 1 => Single p (m+1) T η
  | 2 => Double p (m+1) T η
  | 3 => EqualProd p (m+1) T η

instance targetFinite : (j : Fin 4) → Fintype (Target p m T η j)
  | 0 => inferInstanceAs (Fintype (Mass p (m+1) η))
  | 1 => inferInstanceAs (Fintype (Single p (m+1) T η))
  | 2 => inferInstanceAs (Fintype (Double p (m+1) T η))
  | 3 => inferInstanceAs (Fintype (EqualProd p (m+1) T η))

theorem target_card (j : Fin 4) : Fintype.card (Target p m T η j) = value p (m+1) T η j := by
  fin_cases j
  · exact mass_card p (m+1) T η
  · exact single_card p (m+1) T η
  · exact double_card p (m+1) T η
  · exact equalProd_card p (m+1) T η

/-- Certificates before erasure, including the common endpoint for the collision query. -/
def Transcript : Fin 4 → Type
  | 0 => Mass p (m+1) η
  | 1 => Σ s : Mass p (m+1) η, Checked s.val T
  | 2 => Σ s : Mass p (m+1) η, Checked s.val T × Checked s.val T
  | 3 => Σ s : Mass p (m+1) η, Joined s.val T

noncomputable def erase (mul : w3_modMulInterface) :
    (j : Fin 4) → Transcript p m T η j ≃ Target p m T η j
  | 0 => Equiv.refl _
  | 1 => Equiv.sigmaCongrRight fun s => atomsEquiv mul s.val T
  | 2 => Equiv.sigmaCongrRight fun s => (atomsEquiv mul s.val T).prodCongr (atomsEquiv mul s.val T)
  | 3 => Equiv.sigmaCongrRight fun s => joinedEquiv mul s.val T

end DetDLP.S8G.FpMoment


