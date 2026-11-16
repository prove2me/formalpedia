-- Prove2me | Definitions.Def_AMRangeAvoid_Characterization_Supplement_Grid
-- name    : AMRangeAvoid_Characterization_Supplement_Grid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:24:04.189961+00:00
-- url     : https://prove2.me/theorems/21a58958-7f02-48b5-b224-801e35a1f056
-- title:
--   Closed integer Euclidean balls, lexicographic indexing and machine costs
-- statement:
--   For dimension $n$ and integer radius $R\ge0$, define the finite integer Euclidean ball and its translated intersection by
--
--   $$E_R=\{z\in\mathbb Z^n:\|z\|_2\le R\},\qquad E_R\cap(E_R+w)=\{z\in E_R:\|z-w\|_2\le R\}.$$
--
--   Finite enumeration of the coordinate box followed by exact squared-integer tests defines these sets without any counting oracle. The lexicographic rank counts points preceding the input, using coordinate zero first. The inverse rank selects from the lexicographically sorted finite set. Its default value outside the legal rank range carries no correctness assertion.
--
--   The indexing specification requires three actual finite Turing-machine programs and uniform constants chosen before all dimensions, radii and translations. Counting applies to every integer translation, including empty intersections; ranking and inverse ranking apply to every legal point and rank. All three running times are polynomial in numerical $n+R$, not in $\log R$. The input places dimension and radius before signed coordinates so an oversized coordinate may be rejected from a bounded prefix.
-- source:
--   Zeyong Li, STOC 2027 submission #502 (October 2026), Lemmas 2.15–2.16, printed pp.13–14 (PDF pp.15–16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/502.pdf

import Definitions.Def_AMRangeAvoid_Characterization_Supplement_Lattices

namespace AMRangeAvoid.Characterization.Supplement

/-- All integer coordinates in [-R,R], without any assumed enumeration oracle. -/
def gridBox (n R : ℕ) : Finset (Fin n → ℤ) :=
  (Finset.univ : Finset (Fin n → Fin (2 * R + 1))).image
    (fun z i => (z i : ℤ) - (R : ℤ))

/-- Closed Euclidean ball; integer squared norms give an exact decidable test. -/
def gridBall (n R : ℕ) : Finset (Fin n → ℤ) :=
  (gridBox n R).filter (fun z => ∑ i, z i ^ 2 ≤ (R : ℤ) ^ 2)

/-- z∈E_R and z−w∈E_R, so the translation has the source's positive sign. -/
def gridLens {n : ℕ} (R : ℕ) (w : Fin n → ℤ) : Finset (Fin n → ℤ) :=
  (gridBall n R).filter (fun z => ∑ i, (z i - w i) ^ 2 ≤ (R : ℤ) ^ 2)

def integerEuclidean {n : ℕ} (z : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => (z i : ℝ))

/-- Lexicographic order uses coordinate 0 first. -/
def LexLess {n : ℕ} (a b : Fin n → ℤ) : Prop :=
  ∃ i, a i < b i ∧ ∀ j, j < i → a j = b j

instance {n : ℕ} (a b : Fin n → ℤ) : Decidable (LexLess a b) :=
  inferInstanceAs (Decidable (∃ i, a i < b i ∧ ∀ j, j < i → a j = b j))

def gridRank {n : ℕ} (R : ℕ) (w e : Fin n → ℤ) : ℕ :=
  ((gridLens R w).filter (fun z => LexLess z e)).card

noncomputable def gridUnrank {n : ℕ} (R : ℕ) (w : Fin n → ℤ) (q : ℕ) : Fin n → ℤ :=
  ((gridLens R w).toList.mergeSort (fun a b => decide (¬ LexLess b a))).getD q 0

def intVectorCode {n : ℕ} (z : Fin n → ℤ) : Bits :=
  (List.ofFn (fun i => intCode (z i))).flatten

/-- Count/rank/unrank input modes. n and R precede arbitrary signed coordinates,
so a huge coordinate can be detected by a bounded prefix before its payload is read. -/
def gridInput {n : ℕ} (mode R : ℕ) (w : Fin n → ℤ) (extra : Bits) : Bits :=
  natCode mode ++ natCode n ++ natCode R ++ intVectorCode w ++ extra

/-- Computational content of Lemma 2.16. All three finite programs, the leading
constant, and the exponent are chosen uniformly BEFORE n,R,w,e,q. The radius is
numerical, not its binary length. Out-of-domain ranks are not requested. -/
def GridIndexingAlgorithms : Prop :=
  ∃ count rank unrank : Turing.TM2ComputableAux Bool Bool,
    ∃ C k : ℕ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ R : ℕ, ∀ w : Fin n → ℤ,
      let time := C * (n + R + 1) ^ k
      RunsWithin count (gridInput 0 R w []) (natCode (gridLens R w).card) time ∧
      (∀ e ∈ gridLens R w,
        gridRank R w e < (gridLens R w).card ∧
        gridUnrank R w (gridRank R w e) = e ∧
        RunsWithin rank (gridInput 1 R w (intVectorCode e))
          (natCode (gridRank R w e)) time) ∧
      (∀ q < (gridLens R w).card,
        gridUnrank R w q ∈ gridLens R w ∧
        gridRank R w (gridUnrank R w q) = q ∧
        RunsWithin unrank (gridInput 2 R w (natCode q))
          (intVectorCode (gridUnrank R w q)) time)

end AMRangeAvoid.Characterization.Supplement


