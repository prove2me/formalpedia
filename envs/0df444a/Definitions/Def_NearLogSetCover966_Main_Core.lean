-- Prove2me | Definitions.Def_NearLogSetCover966_Main_Core
-- name    : NearLogSetCover966_Main_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T09:21:23.888808+00:00
-- url     : https://prove2.me/theorems/0fea618c-0e85-414d-a8be-5cc9708182f8
-- title:
--   Finite incidence objects, monotone semantics, binary vector sums and linear separators
-- statement:
--   A Set Cover instance consists of the finite universe $U=\{0,\ldots,u-1\}$ and $N$ indexed subsets. Distinct labels may carry equal or empty sets, and the family need not cover $U$. A cover is a set of labels whose sets contain every universe element. Its optimum is the least cover cardinality in $\mathbb N\cup\{\infty\}$, with value $\infty$ if there is no cover and zero for the empty universe.
--
--   Boolean assignments have Hamming weight equal to their number of true coordinates. An MMSA$_2$ formula is an explicit list of OR clauses joined by an AND. General monotone syntax uses input, AND and OR nodes. The uniform layered MMSA representation additionally has positive input and layer counts, an odd number of non-bottom layers (so total depth is even), and one stored bottom OR clause for every tuple of layer indices. Empty OR is false and empty AND is true. The local acceptance expression for a function $\Phi$ and a set $L$ of assignments is
--
--   $$\mathcal A_L\Phi(x)=\bigwedge_{z\in L}\left(\Phi(z)\lor\bigvee_{a:z_a=0}x_a\right).$$
--
--   A grouped Label Cover input has positive counts $k,n,m,t$ and neighborhoods $P_{r,i,a}\subseteq[t]$. Its value is $\bigwedge_r\bigvee_b\bigwedge_i\bigvee_{a:b\in P_{r,i,a}}x_{i,a}$. Its parameter $p$ is the actual maximum number of distinct neighborhoods within a group and test. Selections are unrestricted subsets of the $kn$ labels. A Vector Sum input contains $k$ groups of $n$ distinct vectors in $\mathbb F_2^D$ and is YES precisely when one vector from each group sums to zero.
--
--   A matrix family $H$ is a $(D,d,A)$ linear separator when every set $Z\subseteq\mathbb F_2^D\setminus\{0\}$ of size at most $A$ is simultaneously avoided by some matrix in $H$. Even $Z=\varnothing$ requires a nonempty family. The definitions supply actual finite encoders, including every matrix/vector/incidence entry, so they can be used in deterministic resource statements.
--
--   **Formalization Note** Set Cover reuses the published incidence instance. The source's number of sets is `sets.length`, whereas the reused field `n` counts universe points. The source encoder's symbols are translated as $\mathtt{none}\mapsto00$, $\mathtt{false}\mapsto01$, $\mathtt{true}\mapsto10$. The decoder rejects $11$, incomplete pairs, malformed headers and wrong row lengths. Other arrays use unary self-delimiting dimension headers and binary entries. Matrix families are ordered lists without repetitions; vectors within each group are distinct. Natural dimensions include zero. The optional general circuit syntax allows arbitrary finite fan-ins; only actual MMSA$_2$ clause lists and grouped MMSA$_4$ inputs enter the reductions.
-- source:
--   Bingkai Lin, Xin Zheng, STOC 2027 submission #966 (October 2026), Definitions 2.3–2.6, printed pp.9–10 (PDF pp.11–12); Definition 3.5, printed p.13 (PDF p.15); §3.1, printed p.12 (PDF p.14)

import Mathlib
import Definitions.Def_SetCoverThreshold_SetCover_Instance

set_option autoImplicit false

namespace NearLogSetCover966.Main

abbrev SCInstance := SetCoverThreshold.SetCover.SCInstance
abbrev Bits (n : ℕ) := Fin n → Bool
abbrev F2 := ZMod 2
abbrev Vec (D : ℕ) := Fin D → F2
abbrev Mat (D d : ℕ) := Matrix (Fin d) (Fin D) F2

noncomputable def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

def weight {n : ℕ} (x : Bits n) : ℕ := (Finset.univ.filter fun i => x i = true).card

noncomputable def localAcceptance {n : ℕ} (L : Set (Bits n)) (Φ : Bits n → Bool)
    (x : Bits n) : Bool :=
  @decide (∀ z ∈ L, Φ z = true ∨ ∃ a : Fin n, z a = false ∧ x a = true)
    (Classical.propDecidable _)

def HasSmallAssignment {n : ℕ} (Φ : Bits n → Bool) (h : ℝ) : Prop :=
  ∃ x : Bits n, Φ x = true ∧ (weight x : ℝ) ≤ h

def NoSmallAssignment {n : ℕ} (Φ : Bits n → Bool) (h : ℝ) : Prop :=
  ∀ x : Bits n, Φ x = true → h < (weight x : ℝ)

/-- Actual AND of OR clauses; empty AND=true and empty OR=false. -/
structure MMSA2 where
  n : ℕ
  clauses : List (Finset (Fin n))

def MMSA2.eval (F : MMSA2) (x : Bits F.n) : Bool :=
  F.clauses.all fun C => decide (∃ i ∈ C, x i = true)

/-- General finite monotone syntax, with ordinary gate semantics. -/
inductive MonotoneCircuit (n : ℕ) where
  | input : Fin n → MonotoneCircuit n
  | andGate : List (MonotoneCircuit n) → MonotoneCircuit n
  | orGate : List (MonotoneCircuit n) → MonotoneCircuit n

def MonotoneCircuit.eval {n : ℕ} (x : Bits n) : MonotoneCircuit n → Bool
  | .input i => x i
  | .andGate fs => fs.attach.all (fun f => MonotoneCircuit.eval x f.val)
  | .orGate fs => fs.attach.any (fun f => MonotoneCircuit.eval x f.val)

termination_by c => sizeOf c
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem f.property; omega

/-- Depth/layer shape of Definition 2.3. Bottom OR may have no inputs. -/
def HasAlternatingShape {n : ℕ} : ℕ → Bool → MonotoneCircuit n → Prop
  | 0, _, .input _ => True
  | 1, false, .orGate fs => ∀ f ∈ fs, HasAlternatingShape 0 true f
  | t + 2, true, .andGate fs => fs ≠ [] ∧ ∀ f ∈ fs, HasAlternatingShape (t + 1) false f
  | t + 2, false, .orGate fs => fs ≠ [] ∧ ∀ f ∈ fs, HasAlternatingShape (t + 1) true f
  | _, _, _ => False

/-- The uniform positive layers of Definition 2.3; depth is fanins.length+1, an even number. -/
structure LayeredMMSA where
  n : ℕ
  n_pos : 0 < n
  fanins : List ℕ
  counts_pos : ∀ m ∈ fanins, 0 < m
  odd_layers : Odd fanins.length
  rows : List (Finset (Fin n))
  rows_length : rows.length = fanins.prod

/-- Mixed-radix indexing selects an actual stored bottom OR clause. -/
def evalLayers {n : ℕ} (rows : List (Finset (Fin n))) (x : Bits n) :
    List ℕ → Bool → ℕ → Bool
  | [], _, rowIndex => decide (∃ a ∈ rows.getD rowIndex ∅, x a = true)
  | m :: ms, isAnd, rowIndex =>
      let values := List.ofFn fun i : Fin m => evalLayers rows x ms (!isAnd) (rowIndex * m + i.val)
      if isAnd then values.all id else values.any id

def LayeredMMSA.eval (F : LayeredMMSA) (x : Bits F.n) : Bool :=
  evalLayers F.rows x F.fanins true 0

structure LabelCover where
  k : ℕ
  n : ℕ
  m : ℕ
  t : ℕ
  k_pos : 0 < k
  n_pos : 0 < n
  m_pos : 0 < m
  t_pos : 0 < t
  P : Fin m → Fin k → Fin n → Finset (Fin t)

abbrev LabelCover.Assignment (F : LabelCover) := Fin F.k → Fin F.n → Bool

def LabelCover.eval (F : LabelCover) (x : F.Assignment) : Bool :=
  decide (∀ r : Fin F.m, ∃ b : Fin F.t, ∀ i : Fin F.k,
    ∃ a : Fin F.n, b ∈ F.P r i a ∧ x i a = true)

def LabelCover.weight (F : LabelCover) (x : F.Assignment) : ℕ :=
  (Finset.univ.filter fun ia : Fin F.k × Fin F.n => x ia.1 ia.2 = true).card

def LabelCover.small (F : LabelCover) (h : ℝ) : Prop :=
  ∃ x, F.eval x = true ∧ (F.weight x : ℝ) ≤ h

def LabelCover.large (F : LabelCover) (h : ℝ) : Prop :=
  ∀ x, F.eval x = true → h < (F.weight x : ℝ)

def LabelCover.p (F : LabelCover) : ℕ :=
  (Finset.univ : Finset (Fin F.m × Fin F.k)).sup fun ri =>
    ((Finset.univ : Finset (Fin F.n)).image (F.P ri.1 ri.2)).card

structure VectorSum where
  k : ℕ
  n : ℕ
  D : ℕ
  v : Fin k → Fin n → Vec D
  distinct : ∀ i, Function.Injective (v i)

def VectorSum.yes (I : VectorSum) : Prop :=
  ∃ a : Fin I.k → Fin I.n, ∑ i : Fin I.k, I.v i (a i) = 0

/-- Ordered, duplicate-free family of actual binary matrices. -/
structure HashFamily (D d : ℕ) where
  maps : List (Mat D d)
  nodup : maps.Nodup

def HashFamily.avoids {D d : ℕ} (H : HashFamily D d) (A : ℝ) : Prop :=
  ∀ Z : Finset (Vec D), (0 : Vec D) ∉ Z → (Z.card : ℝ) ≤ A →
    ∃ ψ ∈ H.maps, ∀ z ∈ Z, ψ.mulVec z ≠ 0

def HashFamily.zeros {D d : ℕ} (H : HashFamily D d) (z : Vec D) : ℕ :=
  (H.maps.filter fun ψ => ψ.mulVec z = 0).length

def coverSmall (I : SCInstance) (h : ℝ) : Prop :=
  ∃ C, I.IsCover C ∧ (C.card : ℝ) ≤ h

def coverLarge (I : SCInstance) (h : ℝ) : Prop :=
  ∀ C, I.IsCover C → h < (C.card : ℝ)

/-- Extended natural optimum, including infinity when no cover exists. -/
noncomputable def coverOpt (I : SCInstance) : WithTop ℕ :=
  sInf {v | ∃ C, I.IsCover C ∧ v = (C.card : WithTop ℕ)}

/-- Unary, self-delimiting natural header. -/
def unary (n : ℕ) : List Bool := List.replicate n true ++ [false]

def frame (x : List Bool) : List Bool := unary x.length ++ x

def optionBits : Option Bool → List Bool
  | none => [false, false]
  | some false => [false, true]
  | some true => [true, false]

def scEncode (I : SCInstance) : List Bool := I.encode.flatMap optionBits

def decodePairs : List Bool → Option (List (Option Bool))
  | [] => some []
  | false :: false :: xs => (decodePairs xs).map (none :: ·)
  | false :: true :: xs => (decodePairs xs).map (some false :: ·)
  | true :: false :: xs => (decodePairs xs).map (some true :: ·)
  | _ => none

def readHeader : List (Option Bool) → Option (ℕ × List (Option Bool))
  | [] => none
  | none :: xs => some (0, xs)
  | some true :: xs => (readHeader xs).map fun r => (r.1 + 1, r.2)
  | some false :: _ => none

def decodeRows (n : ℕ) : ℕ → List (Option Bool) → Option (List (Finset (Fin n)))
  | 0, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, xs =>
    if xs = [] then some [] else
    if xs.length < n + 1 then none else
    if xs[n]? ≠ some none then none else
    if (xs.take n).any (fun b => b.isNone) then none else
      (decodeRows n fuel (xs.drop (n + 1))).map fun ss =>
        (Finset.univ.filter fun i : Fin n => xs[i.val]? = some (some true)) :: ss

def scDecode (x : List Bool) : Option SCInstance := do
  let symbols ← decodePairs x
  let (n, rows) ← readHeader symbols
  let sets ← decodeRows n rows.length rows
  pure ⟨n, sets⟩

def vsEncode (I : VectorSum) : List Bool :=
  unary I.k ++ unary I.n ++ unary I.D ++
    (List.ofFn fun i : Fin I.k => (List.ofFn fun a : Fin I.n =>
      List.ofFn fun j : Fin I.D => decide (I.v i a j = 1)).flatten).flatten

def lcEncode (F : LabelCover) : List Bool :=
  unary F.k ++ unary F.n ++ unary F.m ++ unary F.t ++
    (List.ofFn fun r : Fin F.m => (List.ofFn fun i : Fin F.k =>
      (List.ofFn fun a : Fin F.n => List.ofFn fun b : Fin F.t =>
        decide (b ∈ F.P r i a)).flatten).flatten).flatten

def layeredEncode (F : LayeredMMSA) : List Bool :=
  unary F.n ++ unary F.fanins.length ++ F.fanins.flatMap unary ++
    F.rows.flatMap fun C => List.ofFn fun i : Fin F.n => decide (i ∈ C)

def mmsaEncode (F : MMSA2) : List Bool :=
  unary F.n ++ unary F.clauses.length ++
    F.clauses.flatMap fun C => List.ofFn fun i : Fin F.n => decide (i ∈ C)

def hashEncode {D d : ℕ} (H : HashFamily D d) : List Bool :=
  unary D ++ unary d ++ unary H.maps.length ++ H.maps.flatMap fun ψ =>
    (List.ofFn fun i : Fin d => List.ofFn fun j : Fin D => decide (ψ i j = 1)).flatten

end NearLogSetCover966.Main


