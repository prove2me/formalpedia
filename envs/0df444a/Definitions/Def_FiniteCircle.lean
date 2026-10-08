-- Prove2me | Definitions.Def_FiniteCircle
-- name    : FiniteCircle
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:11.275221+00:00
-- url     : https://prove2.me/theorems/c0a4cc61-2bb6-4efc-818e-3638dbc0a217
-- statement:
--   This block defines edit-distance embedding quantities, binary substitution codes, and two recursive finite-circle constructions, culminating in a defined proposition FullMain. A single edit inserts, deletes, or substitutes one symbol; editDistance(x,y) is the least length of an edit script, lcs(x,y) is the greatest common-subsequence length, and deficit(x,y)=|x|−lcs(x,y). Words(α,d) consists of words of length at most d. For a map into real ℓ¹ indexed by the natural numbers, distortion is the product of the supremum expansion ratio and supremum contraction ratio over distinct domain points, using edit distance between their associated words. Optimal distortion is the infimum over injective maps; E(α,d) applies this to Words(α,d), setDistortion applies it to a set of binary words, and alphabetSupremum(d)=sup_{A≥2}E(Fin A,d). The scale is s(d)=√(log d·log log d). A code c assigns each letter a binary block of length w, and encode concatenates these blocks. SubstitutionBounds(a,C,c) requires 0<w≤C log(2|α|), and, for all equal-length words x,y, a w deficit(x,y)≤deficit(encode(x),encode(y))≤w deficit(x,y); for arbitrary words it also requires encoded edit distance at most w times the original. OffsetLocal(δ,c) requires that any length-⌊w/8⌋ intervals lying within the codewords of distinct letters have common-subsequence length at most (1−δ)⌊w/8⌋. AnchorLocal(ε,c) requires that two increasing lists of matching positions, of equal length at least w/4, with at most εw skipped positions within each list’s span, must come from the same letter and include a matched pair with identical positions. Here a nonempty span is last position minus first position plus one, and the empty span is zero. TwoCodes(a,C,δ,ε) asserts that every finite alphabet of size at least two admits one code satisfying SubstitutionBounds and OffsetLocal and another satisfying SubstitutionBounds and AnchorLocal; their widths may differ. For an integer q and an array p, put P_l=∏_{k<q}p(l,k) and N=2∏_{1≤l≤q}P_l. MaskPrimes requires all q² selected entries to be distinct primes in [q³,2q³], while ExcludedPrimes instead requires them in (q³,q⁵]. At mask level l, tags are pairs (k,b), with k<q and b<p(l,k); alphabets recursively prepend tags to binary symbols, and states are recursively tag-indexed families of elements of ℤ/Nℤ. Shifting a state adds the same circle element to every leaf. The base mask word records whether each circle position minus the state lies in the first ⌊N/2⌋ positions. At level l, concatenate over t=0,…,RP_l−1 and all tags (k,b), prefixing each recursive symbol with its tag and shifting that tag’s state by ∑_{j<q}(N/p(l,j))(t mod p(l,j))+b(N/p(l,k))(t mod p(l,k)), interpreted modulo N. The excluded construction instead uses q child states at each level, prefixes the child index to recursive symbols, and shifts child i by the same sum with j=i omitted; its base symbols retain both the circle position and the binary half-circle indicator. Both recursive word definitions allow general natural-number circle sizes and repetition counts. MaskWitness(a,C,δ,c,d) and ExcludedWitness(a,C,ε,c,d) assert existence of the corresponding prime array with q≥2, a binary code with the respective substitution and local properties, and a common encoded length 0<n≤d for every depth-q state, using circle size N and R=q^(2q); the resulting set of binary words must have optimal distortion at least exp(c s(d)). UniformUpper(C,d₀) requires every finite alphabet of size at least two and every d≥d₀ to admit a finite-dimensional real ℓ¹ map whose pairwise distances lie between edit distance and exp(C s(d)) times edit distance. Finally, FullMain is the proposition that positive constants c,C,a,Ccode,δ,ε and a natural threshold d₀ exist such that TwoCodes(a,Ccode,δ,ε) and UniformUpper(C,d₀) hold, every such alphabet satisfies exp(c s(d))≤E(α,d)≤exp(C s(d)) for d≥d₀, and every d≥d₀ has both witnesses with code constant Ccode and lower-bound constant c, together with the same two-sided bounds on alphabetSupremum(d).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/FiniteCircle.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/FiniteCircle.lean; bytes 16..10094
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace FiniteCircle

open scoped BigOperators List

universe u v

inductive EditStep {α : Type u} : List α → List α → Prop
  | insert (u v : List α) (a : α) : EditStep (u ++ v) (u ++ a :: v)
  | delete (u v : List α) (a : α) : EditStep (u ++ a :: v) (u ++ v)
  | substitute (u v : List α) (a b : α) : EditStep (u ++ a :: v) (u ++ b :: v)

inductive EditScript {α : Type u} : ℕ → List α → List α → Prop
  | nil (x : List α) : EditScript 0 x x
  | cons {n : ℕ} {x y z : List α} :
      EditStep x y → EditScript n y z → EditScript (n + 1) x z

noncomputable def editDistance {α : Type u} (x y : List α) : ℕ :=
  sInf {n : ℕ | EditScript n x y}

noncomputable def lcs {α : Type u} (x y : List α) : ℕ :=
  sSup {n : ℕ | ∃ z : List α, z <+ x ∧ z <+ y ∧ z.length = n}

noncomputable def deficit {α : Type u} (x y : List α) : ℕ := x.length - lcs x y

abbrev Words (α : Type u) (d : ℕ) := {x : List α // x.length ≤ d}
abbrev RealL1 := lp (fun _ : ℕ => ℝ) 1

noncomputable def distortion {α : Type u} {X : Type v} (word : X → List α)
    (f : X → RealL1) : ℝ :=
  (sSup {r : ℝ | ∃ x y : X, x ≠ y ∧
    r = ‖f x - f y‖ / (editDistance (word x) (word y) : ℝ)}) *
  (sSup {r : ℝ | ∃ x y : X, x ≠ y ∧
    r = (editDistance (word x) (word y) : ℝ) / ‖f x - f y‖})

noncomputable def optimalDistortion {α : Type u} {X : Type v}
    (word : X → List α) : ℝ :=
  sInf {D | ∃ f : X → RealL1, Function.Injective f ∧ D = distortion word f}

noncomputable def E (α : Type u) (d : ℕ) : ℝ :=
  optimalDistortion (fun x : Words α d => x.val)

noncomputable def setDistortion (S : Set (List Bool)) : ℝ :=
  optimalDistortion (fun x : S => x.val)

noncomputable def alphabetSupremum (d : ℕ) : ℝ :=
  sSup {r | ∃ A : ℕ, 2 ≤ A ∧ r = E (Fin A) d}

noncomputable def exponentScale (d : ℕ) : ℝ :=
  Real.sqrt (Real.log d * Real.log (Real.log d))

def encode {α : Type u} {w : ℕ} (c : α → Fin w → Bool) (x : List α) : List Bool :=
  x.flatMap (fun a => List.ofFn (c a))

def interval {α : Type u} {w : ℕ} (c : α → Fin w → Bool)
    (a : α) (s len : ℕ) : List Bool :=
  ((List.ofFn (c a)).drop s).take len

def OffsetLocal {α : Type u} {w : ℕ} (δ : ℝ) (c : α → Fin w → Bool) : Prop :=
  ∀ a b : α, a ≠ b → ∀ s t : ℕ,
    s + w / 8 ≤ w → t + w / 8 ≤ w →
    (lcs (interval c a s (w / 8)) (interval c b t (w / 8)) : ℝ) ≤
      (1 - δ) * (w / 8 : ℕ)

def indexSpan {w : ℕ} (is : List (Fin w)) : ℕ :=
  match is with
  | [] => 0
  | i :: js => (js.getLastD i).val + 1 - i.val

def AnchorLocal {α : Type u} {w : ℕ} (ε : ℝ) (c : α → Fin w → Bool) : Prop :=
  ∀ a b : α, ∀ is js : List (Fin w),
    is.Pairwise (fun i j => i.val < j.val) →
    js.Pairwise (fun i j => i.val < j.val) →
    is.length = js.length → (w : ℝ) / 4 ≤ is.length →
    (indexSpan is - is.length : ℕ) ≤ ε * w →
    (indexSpan js - js.length : ℕ) ≤ ε * w →
    (∀ ij ∈ is.zip js, c a ij.1 = c b ij.2) →
    a = b ∧ ∃ i : Fin w, (i, i) ∈ is.zip js

def SubstitutionBounds {α : Type u} [Fintype α] {w : ℕ}
    (a C : ℝ) (c : α → Fin w → Bool) : Prop :=
  0 < w ∧ (w : ℝ) ≤ C * Real.log (2 * Fintype.card α) ∧
  (∀ L : ℕ, ∀ x y : List α, x.length = L → y.length = L →
    a * w * deficit x y ≤ (deficit (encode c x) (encode c y) : ℝ) ∧
    deficit (encode c x) (encode c y) ≤ w * deficit x y) ∧
  (∀ x y : List α, editDistance (encode c x) (encode c y) ≤ w * editDistance x y)

def TwoCodes (a C δ ε : ℝ) : Prop :=
  ∀ (α : Type) [Fintype α], 2 ≤ Fintype.card α →
    (∃ (w : ℕ) (c : α → Fin w → Bool),
      SubstitutionBounds a C c ∧ OffsetLocal δ c) ∧
    (∃ (w : ℕ) (c : α → Fin w → Bool),
      SubstitutionBounds a C c ∧ AnchorLocal ε c)

def period (h : ℕ) (p : ℕ → ℕ → ℕ) (l : ℕ) : ℕ := ∏ k : Fin h, p l k

def circleSize (h : ℕ) (p : ℕ → ℕ → ℕ) : ℕ :=
  2 * ∏ l : Fin h, period h p (l.val + 1)

def MaskPrimes (h : ℕ) (p : ℕ → ℕ → ℕ) : Prop :=
  (∀ l k : Fin h, Nat.Prime (p (l.val + 1) k)) ∧
  Function.Injective (fun lk : Fin h × Fin h => p (lk.1.val + 1) lk.2) ∧
  ∀ l k : Fin h, h ^ 3 ≤ p (l.val + 1) k ∧ p (l.val + 1) k ≤ 2 * h ^ 3

def ExcludedPrimes (m : ℕ) (p : ℕ → ℕ → ℕ) : Prop :=
  (∀ l k : Fin m, Nat.Prime (p (l.val + 1) k)) ∧
  Function.Injective (fun lk : Fin m × Fin m => p (lk.1.val + 1) lk.2) ∧
  ∀ l k : Fin m, m ^ 3 < p (l.val + 1) k ∧ p (l.val + 1) k ≤ m ^ 5

abbrev MaskTag (h : ℕ) (p : ℕ → ℕ → ℕ) (l : ℕ) := Σ k : Fin h, Fin (p l k)

def maskTags (h : ℕ) (p : ℕ → ℕ → ℕ) (l : ℕ) : List (MaskTag h p l) :=
  (List.ofFn fun k : Fin h => List.ofFn fun b : Fin (p l k) => Sigma.mk k b).flatten

def MaskAlphabet (h : ℕ) (p : ℕ → ℕ → ℕ) : ℕ → Type
  | 0 => Bool
  | l + 1 => MaskTag h p (l + 1) × MaskAlphabet h p l

instance maskAlphabetFintype (h : ℕ) (p : ℕ → ℕ → ℕ) (l : ℕ) :
    Fintype (MaskAlphabet h p l) := by
  induction l with
  | zero => exact inferInstanceAs (Fintype Bool)
  | succ l ih => exact @instFintypeProd _ _ inferInstance ih

def MaskState (h : ℕ) (p : ℕ → ℕ → ℕ) (M : ℕ) : ℕ → Type
  | 0 => ZMod M
  | l + 1 => MaskTag h p (l + 1) → MaskState h p M l

def shiftMaskState (h : ℕ) (p : ℕ → ℕ → ℕ) (M : ℕ) :
    (l : ℕ) → MaskState h p M l → ZMod M → MaskState h p M l
  | 0, v, θ => (show ZMod M from v) + θ
  | l + 1, v, θ => fun j => shiftMaskState h p M l (v j) θ

def maskGamma (h : ℕ) (p : ℕ → ℕ → ℕ) (M l a : ℕ)
    (j : MaskTag h p l) : ZMod M :=
  (∑ k : Fin h, ((M / p l k * (a % p l k) : ℕ) : ZMod M)) +
    ((j.2.val * (M / p l j.1) * (a % p l j.1) : ℕ) : ZMod M)

def maskWord (h : ℕ) (p : ℕ → ℕ → ℕ) (R M : ℕ) :
    (l : ℕ) → MaskState h p M l → List (MaskAlphabet h p l)
  | 0, v => (List.range M).map (fun b => decide (((b : ZMod M) - (show ZMod M from v)).val < M / 2))
  | l + 1, v => (List.range (R * period h p (l + 1))).flatMap fun a =>
      (maskTags h p (l + 1)).flatMap fun j =>
        (maskWord h p R M l
          (shiftMaskState h p M l (v j) (maskGamma h p M (l + 1) a j))).map
          (fun x => (j, x))

def ExcludedAlphabet (m L : ℕ) : ℕ → Type
  | 0 => Fin L × Bool
  | l + 1 => Fin m × ExcludedAlphabet m L l

instance excludedAlphabetFintype (m L l : ℕ) : Fintype (ExcludedAlphabet m L l) := by
  induction l with
  | zero => exact inferInstanceAs (Fintype (Fin L × Bool))
  | succ l ih => exact @instFintypeProd _ _ inferInstance ih

def ExcludedState (m L : ℕ) : ℕ → Type
  | 0 => ZMod L
  | l + 1 => Fin m → ExcludedState m L l

def shiftExcludedState (m L : ℕ) :
    (l : ℕ) → ExcludedState m L l → ZMod L → ExcludedState m L l
  | 0, v, θ => (show ZMod L from v) + θ
  | l + 1, v, θ => fun i => shiftExcludedState m L l (v i) θ

def excludedTranslation (m : ℕ) (p : ℕ → ℕ → ℕ) (L l s : ℕ) (i : Fin m) :
    ZMod L := ∑ j ∈ Finset.univ.erase i, ((L / p l j * (s % p l j) : ℕ) : ZMod L)

def excludedWord (m : ℕ) (p : ℕ → ℕ → ℕ) (R L : ℕ) :
    (l : ℕ) → ExcludedState m L l → List (ExcludedAlphabet m L l)
  | 0, v => List.ofFn fun b : Fin L =>
      (b, decide (((b.val : ZMod L) - (show ZMod L from v)).val < L / 2))
  | l + 1, v => (List.range (R * period m p (l + 1))).flatMap fun s =>
      (List.ofFn fun i : Fin m =>
        (excludedWord m p R L l
          (shiftExcludedState m L l (v i) (excludedTranslation m p L (l + 1) s i))).map
          (fun x => (i, x))).flatten

def MaskWitness (a C δ lower : ℝ) (d : ℕ) : Prop :=
  ∃ h : ℕ, 2 ≤ h ∧ ∃ p : ℕ → ℕ → ℕ, MaskPrimes h p ∧
    ∃ (w : ℕ) (c : MaskAlphabet h p h → Fin w → Bool),
      SubstitutionBounds a C c ∧ OffsetLocal δ c ∧
      ∃ n : ℕ, 0 < n ∧ n ≤ d ∧
        (∀ v : MaskState h p (circleSize h p) h,
          (encode c (maskWord h p (h ^ (2 * h)) (circleSize h p) h v)).length = n) ∧
        Real.exp (lower * exponentScale d) ≤ setDistortion
          (Set.range fun v : MaskState h p (circleSize h p) h =>
            encode c (maskWord h p (h ^ (2 * h)) (circleSize h p) h v))

def ExcludedWitness (a C ε lower : ℝ) (d : ℕ) : Prop :=
  ∃ m : ℕ, 2 ≤ m ∧ ∃ p : ℕ → ℕ → ℕ, ExcludedPrimes m p ∧
    ∃ (w : ℕ) (c : ExcludedAlphabet m (circleSize m p) m → Fin w → Bool),
      SubstitutionBounds a C c ∧ AnchorLocal ε c ∧
      ∃ n : ℕ, 0 < n ∧ n ≤ d ∧
        (∀ v : ExcludedState m (circleSize m p) m,
          (encode c (excludedWord m p (m ^ (2 * m)) (circleSize m p) m v)).length = n) ∧
        Real.exp (lower * exponentScale d) ≤ setDistortion
          (Set.range fun v : ExcludedState m (circleSize m p) m =>
            encode c (excludedWord m p (m ^ (2 * m)) (circleSize m p) m v))

def UniformUpper (C : ℝ) (d₀ : ℕ) : Prop :=
  ∀ (α : Type) [Fintype α], 2 ≤ Fintype.card α → ∀ d : ℕ, d₀ ≤ d →
    ∃ (M : ℕ) (F : Words α d → Fin M → ℝ), ∀ x y : Words α d,
      (editDistance x.val y.val : ℝ) ≤ ∑ i, |F x i - F y i| ∧
      (∑ i, |F x i - F y i|) ≤
        Real.exp (C * exponentScale d) * editDistance x.val y.val

def FullMain : Prop :=
  ∃ c C a Ccode δ ε : ℝ, ∃ d₀ : ℕ,
    0 < c ∧ 0 < C ∧ 0 < a ∧ 0 < Ccode ∧ 0 < δ ∧ 0 < ε ∧
    TwoCodes a Ccode δ ε ∧ UniformUpper C d₀ ∧
    (∀ (α : Type) [Fintype α], 2 ≤ Fintype.card α → ∀ d : ℕ, d₀ ≤ d →
      Real.exp (c * exponentScale d) ≤ E α d ∧
      E α d ≤ Real.exp (C * exponentScale d)) ∧
    (∀ d : ℕ, d₀ ≤ d →
      MaskWitness a Ccode δ c d ∧ ExcludedWitness a Ccode ε c d ∧
      Real.exp (c * exponentScale d) ≤ alphabetSupremum d ∧
      alphabetSupremum d ≤ Real.exp (C * exponentScale d))

end FiniteCircle



end OAI


