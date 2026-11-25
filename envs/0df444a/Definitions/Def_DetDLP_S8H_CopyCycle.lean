-- Prove2me | Definitions.Def_DetDLP_S8H_CopyCycle
-- name    : DetDLP_S8H_CopyCycle
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:52:40.481685+00:00
-- url     : https://prove2.me/theorems/bfa27727-04aa-49d5-b2d0-36a903b3d733
-- title:
--   Degree-three copy cycle for factor layouts
-- statement:
--   A degree-three factor-layout copy cycle that fans out a shared Boolean value through a cyclic incidence arrangement.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_W3_FpIncidence

set_option autoImplicit false
namespace DetDLP.S8H.CopyCycle

/-- Give each occurrence its own bit and link it to its successor.  The permutation
    determines the signals: occurrences in one cycle share one Boolean value. -/
abbrev layout {n g : ℕ} (owner : Fin n → Fin g) (next : Equiv.Perm (Fin n)) : w3_FactorLayout where
  ng := g+n
  nb := n
  ne := n+(n+n)
  gate := Fin.addCases (Fin.castAdd n ∘ owner)
    (Fin.addCases (Fin.natAdd g) (Fin.natAdd g))
  bit := Fin.addCases id (Fin.addCases id next)
  rep := Fin.castAdd (n+n)
  rep_bit := fun _ => Fin.addCases_left ..

variable {n g : ℕ} (owner : Fin n → Fin g) (next : Equiv.Perm (Fin n))

private abbrev firstInc (i : Fin n) : Fin (n+(n+n)) := Fin.castAdd _ i
private abbrev leftInc (i : Fin n) : Fin (n+(n+n)) := Fin.natAdd _ (Fin.castAdd _ i)
private abbrev rightInc (i : Fin n) : Fin (n+(n+n)) := Fin.natAdd _ (Fin.natAdd _ i)

attribute [-simp] Fin.natAdd_eq_addNat

@[local simp] private theorem disjoint {a b : ℕ} (x : Fin a) (y : Fin b) :
    Fin.castAdd b x ≠ Fin.natAdd a y := by
  intro h; have hh := congrArg Fin.val h; simp only [Fin.val_castAdd,Fin.val_natAdd] at hh; omega

@[local simp] private theorem disjoint' {a b : ℕ} (x : Fin a) (y : Fin b) :
    Fin.natAdd a y ≠ Fin.castAdd b x := Ne.symm (disjoint x y)

def checks (t : (v : Fin g) → ({i // owner i = v} → Bool) → Bool) :
    w3_factorTest (layout owner next) :=
  Fin.addCases (fun v b => t v (fun i => b ⟨firstInc i.val, by simp [layout,i.property]⟩))
    (fun i b => decide (b ⟨leftInc i,by simp [layout]⟩ = b ⟨rightInc i,by simp [layout]⟩))

theorem checks_iff (t : (v : Fin g) → ({i // owner i = v} → Bool) → Bool) (a : Fin n → Bool) :
    (∀ v, checks owner next t v (fun e => a ((layout owner next).bit e.val)) = true) ↔
      (∀ v, t v (fun i => a i.val) = true) ∧ ∀ i, a i = a (next i) := by
  constructor
  · intro h
    exact ⟨fun v => by simpa [checks,layout] using h (Fin.castAdd n v),
      fun i => by simpa [checks,layout] using h (Fin.natAdd g i)⟩
  · rintro ⟨ht,he⟩ v
    induction v using Fin.addCases with
    | left i => simpa [checks,layout] using ht i
    | right i => simpa [checks,layout] using he i

/-- Each proxy has exactly three incidences, including in a length-one cycle. -/
theorem bitDegree (i : Fin n) : (w3_factorGraph (layout owner next)).deg (Fin.natAdd (g+n) i) = 3 := by
  rw [w3_bitDegree]
  let A := layout owner next
  let F := (List.finRange A.ne).filter fun e => decide (A.bit e = i)
  have H : F.toFinset = {firstInc i,leftInc i,rightInc (next.symm i)} := by
    ext e
    induction e using Fin.addCases with
    | left e => simp [F,A,layout,firstInc,leftInc,rightInc]
    | right e =>
      induction e using Fin.addCases with
      | left e => simp [F,A,layout,firstInc,leftInc,rightInc]
      | right e => simp [F,A,layout,firstInc,leftInc,rightInc,Equiv.apply_eq_iff_eq_symm_apply]
  have hn : F.Nodup := (List.nodup_finRange A.ne).filter _
  change F.length = 3
  rw [← List.toFinset_card_of_nodup hn,H]
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton] <;>
    simp [firstInc,leftInc,rightInc]
  · intro h
    exact disjoint _ _ (Fin.natAdd_injective _ _ h)
  · exact ⟨disjoint _ _,disjoint _ _⟩

attribute [simp] Fin.natAdd_eq_addNat

end DetDLP.S8H.CopyCycle


