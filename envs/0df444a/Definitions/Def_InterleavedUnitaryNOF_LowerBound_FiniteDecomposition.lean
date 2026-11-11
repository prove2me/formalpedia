-- Prove2me | Definitions.Def_InterleavedUnitaryNOF_LowerBound_FiniteDecomposition
-- name    : InterleavedUnitaryNOF_LowerBound_FiniteDecomposition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:12.271715+00:00
-- url     : https://prove2.me/theorems/d75659d5-2b80-4869-9252-3ce276674ee9
-- title:
--   Operational GoodCube and AB-decomposition on finite subdomains
-- statement:
--   Finite Boolean matrices use explicit domains and zero extension, with uniform cardinality-normalized densities, grid norms and row minima. Minimum-degree removal, rectangle density-increment search, single-matrix decomposition and GoodCube are explicit functions. No output bounds are stored as structure fields.
--
--   The AB procedure uses the source recursion, $\eta=1/[4(d+2)^2]$, the residual $G-G[I^*,K^*]$, and the omitted-domain calls. At depth $d$ it splits one-entries into groups of size $\lfloor2^{-d}|I||K|\rfloor$, or uses the exact singleton case for smaller domains. Empty calls return an empty list.
--
--   Finite execution budgets return an option value; the milestone conclusions require eventual stabilization to a successful output, so termination is not assumed. The density-increment subroutine uses exhaustive finite rectangle search instead of an efficiency-oriented implementation; no running-time bound is claimed.
-- source:
--   Haoyu Wang, Pei Wu, Guangxu Yang, STOC 2027 submission #1513 (October 2026), Appendix A, pp.19–22; cited AFK+24 full version, Algorithms 5.1–5.4, https://arxiv.org/html/2311.09095v2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1513.pdf

import Mathlib
import Definitions.Def_InterleavedUnitaryNOF_LowerBound_Regularity

namespace InterleavedUnitaryNOF.LowerBound

/-- Finite domains are explicit subsets; Boolean matrices are zero-extended. -/
noncomputable def finiteDensity {a b : ℕ} (I : Finset (Fin a)) (K : Finset (Fin b))
    (F : Fin a → Fin b → Bool) : ℝ :=
  (∑ x ∈ I, ∑ z ∈ K, bval (F x z)) / ((I.card : ℝ) * K.card)

noncomputable def finiteGrid {a b : ℕ} (I : Finset (Fin a)) (K : Finset (Fin b))
    (F : Fin a → Fin b → Bool) (d : ℕ) : ℝ :=
  Real.rpow
    ((∑ x ∈ I, ∑ x' ∈ I,
      ((∑ z ∈ K, bval (F x z) * bval (F x' z)) / (K.card : ℝ))^d) /
        ((I.card : ℝ)^2)) (1 / (2 * (d : ℝ)))

def finiteRegular {a b : ℕ} (I : Finset (Fin a)) (K : Finset (Fin b))
    (F : Fin a → Fin b → Bool) (ε : ℝ) (d : ℕ) : Prop :=
  finiteGrid I K F d ≤ (1+ε) * finiteDensity I K F

def finiteMinDegree {a b : ℕ} (I : Finset (Fin a)) (K : Finset (Fin b))
    (F : Fin a → Fin b → Bool) (ε : ℝ) : Prop :=
  ∀ x ∈ I, (1-ε) * finiteDensity I K F ≤
    (∑ z ∈ K, bval (F x z)) / (K.card : ℝ)

noncomputable def restrictMatrix {a b : ℕ} (I : Finset (Fin a)) (K : Finset (Fin b))
    (F : Fin a → Fin b → Bool) : Fin a → Fin b → Bool :=
  fun x z => decide (x ∈ I ∧ z ∈ K) && F x z

/-- A finite budget implements each loop approximation; no bound is assumed.
A theorem must establish stabilization to Some output, i.e. termination. -/
noncomputable def minDegreeLoop {a b : ℕ} (K : Finset (Fin b))
    (F : Fin a → Fin b → Bool) (ε γ : ℝ) (initialSize : ℕ) :
    ℕ → Finset (Fin a) → Finset (Fin a)
  | 0, I => I
  | fuel+1, I => by
      classical
      let bad := I.filter (fun x =>
        (∑ z ∈ K, bval (F x z)) / (K.card : ℝ) <
          (1-ε) * finiteDensity I K F)
      exact match bad.toList.head? with
      | none => I
      | some x =>
          let I' := I.erase x
          if (I'.card : ℝ) ≤ (1-γ)*initialSize then I'
          else minDegreeLoop K F ε γ initialSize fuel I'

noncomputable def minDegreeSet {a b : ℕ} (I : Finset (Fin a)) (K : Finset (Fin b))
    (F : Fin a → Fin b → Bool) (ε γ : ℝ) :=
  minDegreeLoop K F ε γ I.card (I.card+1) I

/-- Brute-force density-increment search. No running-time bound is a target.
The subroutine searches rectangles, not GoodCube/AB output certificates. -/
noncomputable def siftRectangle {a b : ℕ} (I : Finset (Fin a)) (K : Finset (Fin b))
    (F : Fin a → Fin b → Bool) (ε : ℝ) (d : ℕ) :
    Option (Finset (Fin a) × Finset (Fin b)) := by
  classical
  exact ((I.powerset.product K.powerset).toList).find? (fun B =>
    decide (B.1.Nonempty ∧ B.2.Nonempty ∧
      (1+ε/2) * finiteDensity I K F ≤ finiteDensity B.1 B.2 F ∧
      ε/16 * (finiteDensity I K F)^(2*d) * I.card * K.card ≤
        (B.1.card : ℝ)*B.2.card))

noncomputable def goodRectangle {a b : ℕ} (F : Fin a → Fin b → Bool)
    (ε : ℝ) (d : ℕ) : ℕ → Finset (Fin a) → Finset (Fin b) →
      Option (Finset (Fin a) × Finset (Fin b))
  | 0, _, _ => none
  | fuel+1, I, K => by
      classical
      let I' := minDegreeSet I K F ε (1/2)
      exact if (1+ε/2)*finiteDensity I K F ≤ finiteDensity I' K F then
        goodRectangle F ε d fuel I' K
      else if finiteRegular I' K F ε d then some (I',K)
      else do
        let B ← siftRectangle I' K F ε d
        goodRectangle F ε d fuel B.1 B.2

structure RectPiece (a b : ℕ) where
  rows : Finset (Fin a)
  cols : Finset (Fin b)
  matrix : Fin a → Fin b → Bool

noncomputable def aDecomposition {a b : ℕ} (ε : ℝ) (d : ℕ) :
    ℕ → Finset (Fin a) → Finset (Fin b) → (Fin a → Fin b → Bool) →
      Option (List (RectPiece a b))
  | 0, _, _, _ => none
  | fuel+1, I, K, F => by
      classical
      exact if I = ∅ ∨ K = ∅ then some []
      else if finiteDensity I K F ≤ Real.rpow 2 (-(d : ℝ)) then
        some [⟨I,K,restrictMatrix I K F⟩]
      else do
        let B ← goodRectangle F ε d fuel I K
        let rest := fun x z => F x z && !decide (x ∈ B.1 ∧ z ∈ B.2)
        let tail ← aDecomposition ε d fuel I K rest
        pure (⟨B.1,B.2,restrictMatrix B.1 B.2 F⟩ :: tail)

structure FinitePiece (a b c : ℕ) where
  I : Finset (Fin a)
  J : Finset (Fin b)
  K : Finset (Fin c)
  F : Fin b → Fin c → Bool
  G : Fin a → Fin c → Bool

structure CubeOutput (a b c : ℕ) where
  Istar : Finset (Fin a)
  Kstar : Finset (Fin c)
  pieces : List (FinitePiece a b c)

/-- A first failing rectangle identifies a recursive call of GoodCube. -/
noncomputable def cubeTest {a b c : ℕ} (I : Finset (Fin a))
    (G : Fin a → Fin c → Bool) (ε η : ℝ) (d : ℕ) (A : RectPiece b c) :
    Option (Finset (Fin a) × Finset (Fin c)) := by
  classical
  let I' := minDegreeSet I A.cols G ε η
  exact if (1+ε*η)*finiteDensity I A.cols G ≤ finiteDensity I' A.cols G then
    some (I',A.cols)
  else if finiteRegular I' A.cols G ε d then none
  else siftRectangle I' A.cols G ε d

noncomputable def goodCube {a b c : ℕ} (ε η : ℝ) (d : ℕ) :
    ℕ → Finset (Fin a) → Finset (Fin b) → Finset (Fin c) →
      (Fin b → Fin c → Bool) → (Fin a → Fin c → Bool) →
      Option (CubeOutput a b c)
  | 0, _, _, _, _, _ => none
  | fuel+1, I, J, K, F, G => by
      classical
      let K' := minDegreeSet K I (fun z x => G x z) (ε*η/2) (1/2)
      exact if (1+ε*η/4)*finiteDensity I K G ≤ finiteDensity I K' G then
        goodCube ε η d fuel I J K' F G
      else do
        let parts ← aDecomposition ε d fuel J K' F
        match (parts.filterMap (cubeTest I G ε η d)).head? with
        | some B => goodCube ε η d fuel B.1 J B.2 F G
        | none =>
          pure ⟨I,K', parts.map (fun A =>
            let I' := minDegreeSet I A.cols G ε η
            ⟨I',A.rows,A.cols,A.matrix,restrictMatrix I' A.cols G⟩)⟩

/-- Terminal splitting of G, exactly including the small-domain singleton case. -/
noncomputable def terminalPieces {a b c : ℕ} (I : Finset (Fin a))
    (J : Finset (Fin b)) (K : Finset (Fin c))
    (F : Fin b → Fin c → Bool) (G : Fin a → Fin c → Bool) (d : ℕ) :
      List (FinitePiece a b c) := by
  classical
  let ones := ((I.product K).filter (fun xz => G xz.1 xz.2)).toList
  exact if 2^d ≤ I.card*K.card then
    (List.toChunks ((I.card*K.card)/(2^d)) ones).map (fun group =>
      ⟨I,J,K,restrictMatrix J K F,fun x z => decide ((x,z) ∈ group)⟩)
  else ones.filterMap (fun xz =>
    let J' := J.filter (fun y => F y xz.2)
    if J'.Nonempty then
      some ⟨{xz.1},J',{xz.2},restrictMatrix J' {xz.2} F,
        restrictMatrix {xz.1} {xz.2} G⟩
    else none)

noncomputable def abDecomposition {a b c : ℕ} (ε : ℝ) (d : ℕ) :
    ℕ → ℕ → Finset (Fin a) → Finset (Fin b) → Finset (Fin c) →
      (Fin b → Fin c → Bool) → (Fin a → Fin c → Bool) →
      Option (List (FinitePiece a b c))
  | 0, _, _, _, _, _, _ => none
  | fuel+1, r, I, J, K, F, G => by
      classical
      exact if I = ∅ ∨ J = ∅ ∨ K = ∅ then some []
      else if finiteDensity I K G ≤ Real.rpow 2 (-(d : ℝ)) then
        some [⟨I,J,K,restrictMatrix J K F,restrictMatrix I K G⟩]
      else if r = d then some (terminalPieces I J K F G d)
      else do
        let out ← goodCube ε (1/(4*((d : ℝ)+2)^2)) d fuel I J K F G
        let children ← out.pieces.mapM (fun A =>
          abDecomposition ε d fuel (r+1) (out.Istar \ A.I) A.J A.K A.F
            (restrictMatrix (out.Istar \ A.I) A.K G))
        let remainder := fun x z => G x z && !decide (x ∈ out.Istar ∧ z ∈ out.Kstar)
        let tail ← abDecomposition ε d fuel r I J K F remainder
        pure (out.pieces ++ children.flatten ++ tail)

end InterleavedUnitaryNOF.LowerBound


