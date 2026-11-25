-- Prove2me | Definitions.Def_DetDLP_S8C_LayoutSum
-- name    : DetDLP_S8C_LayoutSum
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:02:15.098734+00:00
-- url     : https://prove2.me/theorems/bac3837e-d076-48d4-a2f5-2ad1999dae7e
-- title:
--   Degree-preserving disjoint sums of factor layouts
-- statement:
--   Disjoint union of W3 incidence layouts. Component gates and bit nodes are reindexed into consecutive blocks, and a satisfying Boolean assignment splits uniquely into satisfying assignments of both components. Every component incidence multiplicity is preserved exactly, so degree bounds compose without shared-wire degree growth.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_W3_FpIncidence

set_option autoImplicit false
namespace DetDLP.S8C

/-- A map on two consecutive index blocks, preserving the block label. -/
def blockMap {a b c d : ℕ} (f : Fin a → Fin c) (g : Fin b → Fin d) : Fin (a+b) → Fin (c+d) :=
  Fin.addCases (fun i => Fin.castAdd d (f i)) (fun j => Fin.natAdd c (g j))

@[simp] theorem blockMap_left {a b c d : ℕ} (f : Fin a → Fin c) (g : Fin b → Fin d) (i : Fin a) :
    blockMap f g (Fin.castAdd b i) = Fin.castAdd d (f i) := Fin.addCases_left ..
@[simp] theorem blockMap_right {a b c d : ℕ} (f : Fin a → Fin c) (g : Fin b → Fin d) (i : Fin b) :
    blockMap f g (Fin.natAdd a i) = Fin.natAdd c (g i) := Fin.addCases_right ..

def sumLayout (A B : w3_FactorLayout) : w3_FactorLayout where
  ng := A.ng + B.ng
  nb := A.nb + B.nb
  ne := A.ne + B.ne
  gate := blockMap A.gate B.gate
  bit := blockMap A.bit B.bit
  rep := blockMap A.rep B.rep
  rep_bit i := by cases i using Fin.addCases <;> simp [A.rep_bit,B.rep_bit]

abbrev Holds (A : w3_FactorLayout) (t : w3_factorTest A) (x : Fin A.nb → Bool) :=
  ∀ g, t g (fun e => x (A.bit e.val)) = true

def sumTests {A B : w3_FactorLayout} (t : w3_factorTest A) (u : w3_factorTest B) :
    w3_factorTest (sumLayout A B) :=
  Fin.addCases (fun g f => t g fun e => f ⟨Fin.castAdd B.ne e.1, by simp [sumLayout,e.2]⟩)
    (fun g f => u g fun e => f ⟨Fin.natAdd A.ne e.1, by simp [sumLayout,e.2]⟩)

theorem sumTests_iff {A B : w3_FactorLayout} (t : w3_factorTest A) (u : w3_factorTest B)
    (x : Fin (A.nb+B.nb) → Bool) : Holds _ (sumTests t u) x ↔
    Holds A t (x ∘ Fin.castAdd B.nb) ∧ Holds B u (x ∘ Fin.natAdd A.nb) := by
  constructor
  · intro h
    exact ⟨fun g => by simpa [sumTests,sumLayout] using h (Fin.castAdd B.ng g),
      fun g => by simpa [sumTests,sumLayout] using h (Fin.natAdd A.ng g)⟩
  · rintro ⟨h,k⟩ g
    change Fin (A.ng+B.ng) at g
    cases g using Fin.addCases with
    | left g => simpa [sumTests,sumLayout] using h g
    | right g => simpa [sumTests,sumLayout] using k g

/-- Splitting a satisfying assignment introduces neither choices nor multiplicity. -/
def sumEquiv {A B : w3_FactorLayout} (t : w3_factorTest A) (u : w3_factorTest B) :
    {x // Holds _ (sumTests t u) x} ≃ ({x // Holds A t x} × {x // Holds B u x}) where
  toFun x := ⟨⟨fun i => x.val (Fin.castAdd B.nb i),((sumTests_iff t u x.val).mp x.2).1⟩,
    ⟨fun i => x.val (Fin.natAdd A.nb i),((sumTests_iff t u x.val).mp x.2).2⟩⟩
  invFun p := ⟨Fin.addCases p.1.val p.2.val, (sumTests_iff ..).mpr ⟨by simpa [Function.comp_def] using p.1.2, by simpa [Function.comp_def] using p.2.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    change Fin (A.nb+B.nb) at i
    cases i using Fin.addCases with
    | left i => simp [Fin.addCases_left]
    | right i => simp [Fin.addCases_right]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext; funext i; simp [Fin.addCases_left]
    · apply Subtype.ext; funext i; simp [Fin.addCases_right]

/-- Exact multiplicity of one output of an incidence map. -/
def multiplicity {a c : ℕ} (f : Fin a → Fin c) (i : Fin c) :=
  ((List.finRange a).filter (fun j => decide (f j = i))).length

private theorem finRange_add (a b : ℕ) : List.finRange (a+b) =
    (List.finRange a).map (Fin.castAdd b) ++ (List.finRange b).map (Fin.natAdd a) := by
  have H := @List.ofFn_add (Fin (a+b)) a b id
  simp only [List.ofFn_eq_map, Function.comp_def, id_eq, List.map_id_fun] at H
  exact H


private theorem disj {a b : ℕ} (i : Fin a) (j : Fin b) : Fin.castAdd b i ≠ Fin.natAdd a j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

@[simp] theorem multiplicity_left {a b c d : ℕ} (f : Fin a → Fin c) (g : Fin b → Fin d) (i : Fin c) :
    multiplicity (blockMap f g) (Fin.castAdd d i) = multiplicity f i := by
  simp [multiplicity,finRange_add a b,List.filter_map,Function.comp_def,Ne.symm (disj _ _)]

@[simp] theorem multiplicity_right {a b c d : ℕ} (f : Fin a → Fin c) (g : Fin b → Fin d) (i : Fin d) :
    multiplicity (blockMap f g) (Fin.natAdd c i) = multiplicity g i := by
  simp [multiplicity,finRange_add a b,List.filter_map,Function.comp_def,disj]

theorem sumDegrees (A B : w3_FactorLayout) :
    (∀ i, multiplicity (sumLayout A B).gate (Fin.castAdd B.ng i) = multiplicity A.gate i) ∧
    (∀ i, multiplicity (sumLayout A B).gate (Fin.natAdd A.ng i) = multiplicity B.gate i) ∧
    (∀ i, multiplicity (sumLayout A B).bit (Fin.castAdd B.nb i) = multiplicity A.bit i) ∧
    (∀ i, multiplicity (sumLayout A B).bit (Fin.natAdd A.nb i) = multiplicity B.bit i) := by
  simp [sumLayout]

end DetDLP.S8C


