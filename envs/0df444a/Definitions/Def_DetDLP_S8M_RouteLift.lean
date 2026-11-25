-- Prove2me | Definitions.Def_DetDLP_S8M_RouteLift
-- name    : DetDLP_S8M_RouteLift
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T05:43:55.653246+00:00
-- url     : https://prove2.me/theorems/cbc9b3e2-878f-52eb-8484-3d69e7ac0bed
-- title:
--   Flattened register routes
-- statement:
--   Identifies routed atom addresses and preserves fitting under concatenation and repeated joins.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8M_AtomMapNat

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.S8M.RouteLift
open S8H0 RegisterMap NamedBlocks GateRoutes S8H.MakeCombinators DetDLP.S8M.Routes DetDLP.S8M.AtomMapNat

theorem pair_val {n m : ℕ} (i : Fin n) (j : Fin m) : (finProdFinEquiv (i,j)).val = j.val+m*i.val := rfl
theorem idxV {n : ℕ} {s : Shape} (i : Fin n) (a : Addr s) : (Addr.vec i a).index.val = i.val*s.size+a.index.val := by
  change a.index.val+s.size*i.val=_; ac_rfl
theorem idxL {s t : Shape} (a : Addr s) : (Addr.fst (v:=t) a).index.val=a.index.val := rfl
theorem idxR {s t : Shape} (a : Addr t) : (Addr.snd (u:=s) a).index.val=s.size+a.index.val := rfl

theorem atom_at {m d e : ℕ} (i : Fin (2*m)) (a : Addr (ECAtomSlot.slotShape d e)) :
    (Routes.A i a).index.val = i.val*(122*d+14*e+46)+a.index.val := by
  change a.index.val + (ECAtomSlot.slotShape d e).size * i.val = _
  have hs := AtomMapNat.slot_size d e
  exact (Nat.add_comm ..).trans (congrArg (· + a.index.val) ((Nat.mul_comm ..).trans (congrArg (i.val * ·) hs)))

theorem address_index_fin {t : Shape} (j : Fin t.size) :
    (ECAtomSlot.address t j).index.val = j.val := by
  induction t with
  | bit => have hj := j.isLt; change j.val < 1 at hj; simp [ECAtomSlot.address, Addr.index]; omega
  | word n => rfl
  | pair l r ihl ihr =>
      by_cases hj : j.val < l.size
      · simp only [ECAtomSlot.address, dif_pos hj, idxL]; exact ihl ⟨j.val, hj⟩
      · simp only [ECAtomSlot.address, dif_neg hj, idxR]; have := ihr ⟨j.val - l.size, by have := j.isLt; change j.val < l.size + r.size at this; omega⟩; dsimp at this; omega
  | vec n t ih =>
      simp only [ECAtomSlot.address, idxV, ih]
      change ((finProdFinEquiv.symm j).1.val * t.size + (finProdFinEquiv.symm j).2.val) = j.val
      have h := congrArg Fin.val (finProdFinEquiv.apply_symm_apply j)
      exact (Nat.add_comm ..).trans ((congrArg (_ + ·) (Nat.mul_comm ..)).trans h)

theorem route_val {l s : Shape} (path : GateRoutes.Path l s)
    (o : ℕ) (hpath : ∀ a, (path a).index.val = o + a.index.val)
    (k : Fin (l.size+1)) :
    (ECAtomSlot.route path k).val = if k.val = l.size then s.size else o + k.val := by
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simp [ECAtomSlot.route]
  · simp only [ECAtomSlot.route, Fin.lastCases_castSucc, Fin.val_castSucc, hpath, address_index_fin]
    rw [if_neg (Nat.ne_of_lt j.isLt)]

theorem cat_map_spec {k l : ℕ} {f : Fin k → Fin l} {a b : NC} {u v : B k}
    (ha : Fits a ⟨u.core, f ∘ u.name⟩) (hb : Fits b ⟨v.core, f ∘ v.name⟩) :
    Fits (catN a b) ⟨(joinB u v).core, f ∘ (joinB u v).name⟩ := by
  have H := cat_spec ha hb
  refine ⟨H.1, fun i => (H.2 i).trans ?_⟩
  change (Fin.addCases (motive := fun _ => Fin l) (f ∘ u.name) (f ∘ v.name) i).val = (f (Fin.addCases (motive := fun _ => Fin k) u.name v.name i)).val
  induction i using Fin.addCases <;> simp

theorem many_map_spec {k l : ℕ} (n : ℕ) {f : Fin k → Fin l} (a : ℕ → NC) (b : Fin (n+1) → B k)
    (h : ∀ j : Fin (n+1), Fits (a j) ⟨(b j).core, f ∘ (b j).name⟩) :
    Fits (manyN n a) ⟨(RangeRows.many n b).core, f ∘ (RangeRows.many n b).name⟩ := by
  induction n generalizing a with
  | zero => rw [manyN_zero]; exact h 0
  | succ n ih => rw [manyN_succ]; exact cat_map_spec (h 0) (ih _ _ fun j => h j.succ)

theorem fits_of_map {k l : ℕ} {f : Fin k → Fin l} {c : NC} {b : B k} {fn : ℕ → ℕ}
    (hb : Fits c b) (hf : ∀ i : Fin b.core.A.ne, fn i = (f (b.name i)).val) :
    Fits (c.1, fn) ⟨b.core, f ∘ b.name⟩ := ⟨hb.1, hf⟩

end DetDLP.S8M.RouteLift


