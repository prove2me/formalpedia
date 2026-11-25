-- Prove2me | Definitions.Def_DetDLP_S8B_Descent
-- name    : DetDLP_S8B_Descent
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:32:51.213933+00:00
-- url     : https://prove2.me/theorems/1b199380-ed9f-4d42-8605-9e64bbf0338e
-- title:
--   Moment-guided prefix descent returns the encoded word of a winning seed
-- statement:
--   The Boolean decision on exact moment tables agrees with conditional-potential descent on every prefix slice. The slice selected at full length is nonempty and contains a winner whose encoding equals the computed word; no injectivity assumption is necessary.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2, Theorem 3.1 (pp. 11–13)

import Definitions.Def_DetDLP_M89_S1_Queries
import Definitions.Def_DetDLP_S8B_MomentCompare

set_option autoImplicit false
namespace DetDLP.S8B
open M89S1 M89SeedSelection
abbrev W := List Bool

def slice {α : Type} [Fintype α] {L : ℕ} (bits : α → Fin L → Bool) (w : W) : Finset α :=
  Finset.univ.filter (fun s => (List.ofFn (bits s)).take w.length = w)

private theorem take_next (w : W) (k : ℕ) (h : k < w.length) :
    w.take (k+1) = w.take k ++ [w[k]] := by
  induction k generalizing w with
  | zero => cases w with | nil => exact False.elim (Nat.not_lt_zero _ h) | cons b l => rfl
  | succ k ih => cases w with
    | nil => simp at h
    | cons a v => simpa using ih v (by simpa using h)

theorem slice_child {α : Type} [Fintype α] {L : ℕ} (bits : α → Fin L → Bool) (w : W) (v : Bool) (h : w.length < L) :
    child bits (w.length,slice bits w) v = ((w++[v]).length,slice bits (w++[v])) := by
  classical
  refine Prod.ext (by simp [child]) ?_
  ext s
  simp only [child,dif_pos h,Finset.mem_filter,slice,Finset.mem_univ,true_and,List.length_append,List.length_singleton]
  rw [take_next _ _ (by simpa using h)]
  simp

def path (next : W → Bool) : ℕ → W
  | 0 => []
  | k+1 => let w := path next k; w ++ [next w]

@[simp] theorem path_len (next : W → Bool) (n : ℕ) : (path next n).length = n := by
  induction n with | zero => rfl | succ n ih => simp [path,ih]

/-- No injectivity hypothesis is needed to output the word of a winning seed. -/
theorem path_winner {α : Type} [Fintype α] [Nonempty α] {L : ℕ} (bits : α → Fin L → Bool) (cost : α → ℝ)
    (next : W → Bool) (hnext : ∀ w, w.length < L → next w = goRight (fun v => (slice bits v).card)
      (fun v => ∑ s ∈ slice bits v, cost s) (w++[false]) (w++[true])) :
    ∃ s ∈ winners bits cost, List.ofFn (bits s) = path next L := by
  classical
  let count (a : Node α) := a.2.card
  let weight (a : Node α) := ∑ s ∈ a.2, cost s
  let node (w : W) : Node α := (w.length,slice bits w)
  let descend := M89SeedSelection.descend count weight (child bits)
  have step (w : W) (h : w.length < L) :
      child bits (node w) (goRight count weight (child bits (node w) false) (child bits (node w) true)) = node (w++[next w]) := by
    have eq (v) := slice_child bits w v h
    change child bits (w.length,slice bits w) _ = _
    rw [show (child bits (node w) false) = node (w++[false]) from eq false,
        show (child bits (node w) true) = node (w++[true]) from eq true, hnext w h]
    exact eq _
  have run (n k : ℕ) (hk : n+k=L) : descend n (node (path next k)) = node (path next L) := by
    induction n generalizing k with
    | zero => simp_all [descend,M89SeedSelection.descend]
    | succ n ih =>
      have h : (path next k).length < L := by simp; omega
      change descend n (child bits _ _) = _
      rw [step _ h]; exact ih (k+1) (by omega)
  have nonempty (k : ℕ) (hk : k ≤ L) : (slice bits (path next k)).Nonempty := by
    induction k with
    | zero => simp [slice,path]
    | succ k ih =>
      let w := path next k
      have hl : w.length < L := by simp [w]; omega
      obtain ⟨s,hs⟩ := ih (by omega)
      have hchild : ∃ b, s ∈ slice bits (w++[b]) := by
        refine ⟨bits s ⟨w.length,hl⟩,?_⟩
        rw [←show (child bits (node w) (bits s ⟨w.length,hl⟩)).2 = slice bits (w++[bits s ⟨w.length,hl⟩]) from congrArg Prod.snd (slice_child bits w _ hl)]
        simpa [node,child,hl] using hs
      change (slice bits (w++[next w])).Nonempty
      rw [hnext w hl]; unfold goRight
      by_cases h0 : (slice bits (w++[false])).card = 0
      · simp only [h0,true_or,decide_true]
        obtain ⟨b,hb⟩ := hchild
        cases b
        · exact False.elim ((Finset.card_pos.mpr ⟨s,hb⟩).ne' h0)
        · exact ⟨s,hb⟩
      · by_cases hr : (slice bits (w++[true])).card = 0
        · simpa [h0,hr] using (Finset.card_pos.mp (Nat.pos_of_ne_zero h0))
        · have all (bit : Bool) : (slice bits (w++[bit])).Nonempty := by
            cases bit <;> exact Finset.card_pos.mp (Nat.pos_of_ne_zero (by assumption))
          exact all _
  have hroot : node [] = (0,Finset.univ) := by simp [node,slice]
  have hw : winners bits cost = slice bits (path next L) := by
    change (descend L (0,Finset.univ)).2 = _
    rw [←hroot]; exact congrArg Prod.snd (run L 0 (by omega))
  obtain ⟨s,hs⟩ := nonempty L le_rfl
  refine ⟨s,hw ▸ hs,?_⟩
  have ht : (List.ofFn (bits s)).take L = path next L := by simpa [slice] using hs
  rwa [List.take_of_length_le (by simp)] at ht

/-- The four oracle moments yield exactly the scaled sum of the potentials on a slice. -/
theorem sum_potential {α : Type} [Fintype α] {L : ℕ} (bits : α → Fin L → Bool) (w : W)
    (sz energy : α → ℕ) (g d u : ℕ) (hd : 0 < d) (hu : 0 < u) :
    let μ := (u : ℝ)/d
    let M := fun (i : Fin 4) => moment bits sz energy i w
    (∑ s ∈ slice bits w, ((g : ℝ) * energy s + 64 * ((sz s : ℝ) - μ)^2)/μ^2) * (u:ℝ)^2 =
      (posPart d g (M 2) (M 3) : ℝ) - negPart d u (M 1) + 64 * (u:ℝ)^2 * (M 0) := by
  classical
  dsimp only
  have local_eq (s : α) : ((g : ℝ) * energy s + 64 * ((sz s : ℝ)-(u:ℝ)/d)^2)/((u:ℝ)/d)^2*(u:ℝ)^2 =
      (d:ℝ)^2*g*energy s + 64*(d:ℝ)^2*(sz s:ℝ)^2-128*d*(u:ℝ)*sz s + 64*(u:ℝ)^2 := by
    field_simp; ring
  rw [Finset.sum_mul]; simp_rw [local_eq]
  simp only [moment, show (0:Fin 4) ≠ 1 by decide, show (1:Fin 4) ≠ 0 by decide,
    show (2:Fin 4) ≠ 0 by decide,show (2:Fin 4) ≠ 1 by decide,show (3:Fin 4) ≠ 0 by decide,
    show (3:Fin 4) ≠ 1 by decide,show (3:Fin 4) ≠ 2 by decide,if_false,if_true,slice]
  simp [posPart,negPart,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum]; ring

def fromMoments (d u g : ℕ) (M : Fin 4 → W → ℕ) (w : W) :=
  let l := w ++ [false]; let r := w ++ [true]
  momentRight d u g (M 0 l) (M 1 l) (M 2 l) (M 3 l) (M 0 r) (M 1 r) (M 2 r) (M 3 r)

theorem fromMoments_spec {α : Type} [Fintype α] {L : ℕ} (bits : α → Fin L → Bool)
    (w : W) (sz energy : α → ℕ) (g d u : ℕ) (hd : 0 < d) (hu : 0 < u) :
    let μ := (u : ℝ)/d
    let f := fun s => ((g : ℝ) * energy s + 64 * ((sz s : ℝ)-μ)^2)/μ^2
    fromMoments d u g (moment bits sz energy) w = goRight (fun v => (slice bits v).card)
      (fun v => ∑ s ∈ slice bits v, f s) (w++[false]) (w++[true]) := by
  classical
  intro μ f
  let M := moment bits sz energy
  let C (v : W) := ∑ s ∈ slice bits v, f s
  let P (v : W) : ℤ := (posPart d g (M 2 v) (M 3 v) : ℤ) - negPart d u (M 1 v)
  have mass (v : W) : M 0 v = (slice bits v).card := by simp [M,moment,slice]
  have hs (v : W) : C v * (u:ℝ)^2 = (P v : ℝ) + 64 * (u:ℝ)^2 * M 0 v := by
    simpa [P, M,C,f,μ] using sum_potential bits v sz energy g d u hd hu
  let l := w++[false]; let r := w++[true]
  apply Bool.eq_iff_iff.mpr
  change (momentRight .. = true) ↔ _
  rw [momentRight_spec]; simp only [goRight, decide_eq_true_eq]
  change (M 0 l = 0 ∨ M 0 r ≠ 0 ∧ P r * ↑(M 0 l) < P l * ↑(M 0 r)) ↔
    ((slice bits l).card = 0 ∨ (slice bits r).card ≠ 0 ∧ C r * (slice bits l).card < C l * (slice bits r).card)
  rw [←mass,←mass]
  apply or_congr_right; apply and_congr_right; intro _
  have hpos : 0 < (u:ℝ)^2 := by positivity
  conv_rhs => rw [←mul_lt_mul_iff_left₀ hpos]
  have E (a b : W) : C a * (M 0 b:ℝ) * (u:ℝ)^2 = (P a:ℝ) * (M 0 b:ℝ) + 64*(u:ℝ)^2*M 0 a*M 0 b := by
    linarith only [congrArg (· * (M 0 b : ℝ)) (hs a)]
  rw [E,E,show 64*(u:ℝ)^2*M 0 l*M 0 r = 64*(u:ℝ)^2*M 0 r*M 0 l by ring,add_lt_add_iff_right]
  exact_mod_cast Iff.rfl

end DetDLP.S8B


