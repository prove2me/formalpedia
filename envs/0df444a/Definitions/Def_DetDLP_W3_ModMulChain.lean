-- Prove2me | Definitions.Def_DetDLP_W3_ModMulChain
-- name    : DetDLP_W3_ModMulChain
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T01:14:08.031785+00:00
-- url     : https://prove2.me/theorems/c8de608c-22b9-4bb1-8716-7c54ebabe200
-- title:
--   Unique M5 runs for a finite sequence of strict-modulus products
-- statement:
--   For a modulus strictly less than the word capacity, a product chain exposes each intermediate remainder together with its two full M5 multiplication witnesses. A completed chain yields the canonical residue of the product; conversely, that residue determines a unique complete chain of remainders and physical assignments.

import Definitions.Def_DetDLP_W3_ModMul

set_option autoImplicit false
namespace DetDLP

/-- At a strict modulus, one staged operation exposes its remainder with the M5 certificate. -/
abbrev w3_mulStage (d : ℕ) (hd : 1 ≤ d) (p : ℕ) :=
  Fin p × Fin (2^d) × w3_mulRun d hd × w3_mulRun d hd

def w3_checkStages {p d : ℕ} (hd : 1 ≤ d) (x : Fin p) :
    List (Fin p) → List (w3_mulStage d hd p) → Fin p → Prop
  | [], [], z => z = x
  | y :: ys, s :: ss, z => w3_modTwo hd p x.val y.val s.1.val s.2 ∧ w3_checkStages hd s.1 ys ss z
  | _, _, _ => False

theorem w3_checkStages_output {p d : ℕ} (hd : 1 ≤ d) (hp : 2 ≤ p) (hfit : p < 2^d)
    (mul : w3_modMulInterface) (x : Fin p) (ys : List (Fin p)) (ss : List (w3_mulStage d hd p))
    (z : Fin p) (ok : w3_checkStages hd x ys ss z) : z.val = (x.val * (ys.map Fin.val).prod) % p := by
  induction ys generalizing x ss with
  | nil =>
    cases ss with
    | nil => change z = x at ok; simp [ok,Nat.mod_eq_of_lt x.isLt]
    | cons => exact False.elim ok
  | cons y ys ih =>
    cases ss with
    | nil => exact False.elim ok
    | cons s ss =>
      obtain ⟨h1,h2⟩ := ok
      have he := ((mul d hd p x.val y.val s.1.val hp hfit.le x.isLt y.isLt s.1.isLt).2 hfit).2 _ h1
      rw [ih s.1 ss h2, he]
      simp [Nat.mod_mul_mod, Nat.mul_assoc]

theorem w3_checkStages_existsUnique {p d : ℕ} (hd : 1 ≤ d) (hp : 2 ≤ p) (hfit : p < 2^d)
    (mul : w3_modMulInterface) (x : Fin p) (ys : List (Fin p)) (z : Fin p)
    (hz : z.val = (x.val * (ys.map Fin.val).prod) % p) :
    ∃! ss, w3_checkStages hd x ys ss z := by
  induction ys generalizing x with
  | nil =>
    have he : z = x := Fin.ext (by simpa [Nat.mod_eq_of_lt x.isLt] using hz)
    refine ⟨[],he,?_⟩
    intro ss ok; cases ss with
    | nil => rfl
    | cons => exact False.elim ok
  | cons y ys ih =>
    let t : Fin p := ⟨(x.val * y.val)%p, Nat.mod_lt _ (by omega)⟩
    have step := ((mul d hd p x.val y.val t.val hp hfit.le x.isLt y.isLt t.isLt).2 hfit).1 rfl
    obtain ⟨r,hr,ur⟩ := step
    have tail : z.val = (t.val*(ys.map Fin.val).prod)%p := by
      simpa [t,Nat.mod_mul_mod,Nat.mul_assoc] using hz
    obtain ⟨ss,hs,us⟩ := ih t tail
    refine ⟨(t,r)::ss, ⟨hr,hs⟩, ?_⟩
    intro cand ok
    cases cand with
    | nil => exact False.elim ok
    | cons s rest =>
      obtain ⟨a,b⟩ := s
      obtain ⟨hm,hrem⟩ := ok
      have ha : a = t := Fin.ext (((mul d hd p x.val y.val a.val hp hfit.le x.isLt y.isLt a.isLt).2 hfit).2 _ hm)
      subst a
      rw [ur b hm, us rest hrem]

end DetDLP


