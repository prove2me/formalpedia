-- Prove2me | Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
-- name    : OAI_Combinatorics_FiniteCircle_CircleWords
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T12:40:21.520991+00:00
-- url     : https://prove2.me/theorems/ca67110a-9c36-436b-bd63-ce4c47a71349
-- title:
--   Lengths and rows of the mask words, half-circle bits and subcircle embeddings
-- statement:
--   Throughout, $h\in\mathbb{N}$, $p(l,k)$ is a table of natural numbers indexed by a level $l$ and an index $k<h$, and $M,R\in\mathbb{N}$. A *mask tag* of level $l$ is a pair $(k,b)$ with $k<h$ and $0\le b<p(l,k)$; $\mathcal{T}_l$ is the list of all mask tags of level $l$ in lexicographic order, and $P_l=\prod_{k<h}p(l,k)$ is the period of level $l$. A mask state of level $0$ is a residue $v\in\mathbb{Z}/M$, and a mask state of level $l+1$ assigns a state $v_j$ of level $l$ to every tag $j$ of level $l+1$; adding $\theta\in\mathbb{Z}/M$ to a state adds $\theta$ to all residues it contains. The level-$0$ mask word $W_0(v)$ is the binary word of length $M$ whose letter in position $b\in\{0,\dots,M-1\}$ is $1$ exactly when the least nonnegative residue of $b-v$ modulo $M$ is smaller than $\lfloor M/2\rfloor$, and
--
--   $$
--   W_{l+1}(v)=\prod_{a=0}^{RP_{l+1}-1}\ \prod_{j\in\mathcal{T}_{l+1}} j\otimes W_l\bigl(v_j+\gamma_{l+1}(a,j)\bigr),
--   $$
--
--   where the products are concatenations in the indicated order, $j\otimes u$ labels every letter of the word $u$ with the tag $j$ (so letters of $W_l$ are tuples of tags ending in a bit), and for a tag $j=(k',b)$ of level $l$
--
--   $$
--   \gamma_l(a,j)=\sum_{k<h}\frac{M}{p(l,k)}\,\bigl(a\bmod p(l,k)\bigr)+b\,\frac{M}{p(l,k')}\,\bigl(a\bmod p(l,k')\bigr)\in\mathbb{Z}/M,
--   $$
--
--   with $M/p$ denoting integer division.
--
--   The module defines the following objects and records their basic properties.
--
--   1. **Mask lengths.** $L_0=M$ and $L_{l+1}=R\,P_{l+1}\,|\mathcal{T}_{l+1}|\,L_l$. Every mask word of level $l$ has length exactly $L_l$, whatever its state. Along the way: every tag of level $l$ occurs in $\mathcal{T}_l$, $|\mathcal{T}_l|=\sum_{k<h}p(l,k)$, and adding $0$ to a state does not change it.
--   2. **Mask rows.** For a state $v$ of level $l+1$ and $a\in\mathbb{N}$, the $a$-th row is $\operatorname{row}_a(v)=\prod_{j\in\mathcal{T}_{l+1}} j\otimes W_l\bigl(v_j+\gamma_{l+1}(a,j)\bigr)$, of length $|\mathcal{T}_{l+1}|\,L_l$; thus $W_{l+1}(v)$ is the concatenation of the rows $a=0,\dots,RP_{l+1}-1$.
--   3. **Half-circle bits.** For $v,b\in\mathbb{Z}/M$, $\beta_v(b)=1$ if the least nonnegative residue of $b-v$ is smaller than $\lfloor M/2\rfloor$ and $\beta_v(b)=0$ otherwise. So $b\mapsto\beta_v(b)$ is the indicator of the half-circle $\{v,v+1,\dots,v+\lfloor M/2\rfloor-1\}$, and $W_0(v)$ lists the values $\beta_v(0),\dots,\beta_v(M-1)$.
--   4. **Half-circle Hamming distance.** For $M\ge1$ and $v,w\in\mathbb{Z}/M$,
--   $$
--   \operatorname{hh}(v,w)=\#\{\,b\in\mathbb{Z}/M:\ \beta_v(b)\ne\beta_w(b)\,\},
--   $$
--   the Hamming distance between $W_0(v)$ and $W_0(w)$; for even $M$ it equals twice the circular distance between $v$ and $w$.
--   5. **Subcircle embeddings.** For $p\mid M$, the map $\iota_p:\mathbb{Z}/p\to\mathbb{Z}/M$, $a\mapsto(M/p)\,a$, is a well-defined group homomorphism (because $p\cdot(M/p)=M$) identifying $\mathbb{Z}/p$ with the multiples of $M/p$. For $p\ge1$ it sends $a$ to the class of $(M/p)\,\bar a$, where $\bar a\in\{0,\dots,p-1\}$ is the least nonnegative representative.
--
--   The common length $L_l$ is what makes the family of mask words an equal-length family, as required of the binary lower-bound witnesses. Rows are the units in which alignments of two mask words are analysed. The half-circle bits connect rotations of the base circle with Hamming and deficit distances, and the subcircle embeddings place the residue groups of the primes $p(l,k)$ inside $\mathbb{Z}/M$, which is how the shifts $\gamma_l$ are written as group homomorphisms.
--
--   **Formalization Note** The table $p$ is a function `ℕ → ℕ → ℕ`, mask tags are `Σ k : Fin h, Fin (p l k)`, and states and words are the recursive definitions `MaskState`, `maskWord`, `shiftMaskState` and `maskGamma` of the base file. The new definitions are `maskLength`, `maskRow`, `halfBit`, `halfHamming` (which needs `NeZero M` so that $\mathbb{Z}/M$ is a finite type) and `subcircle`, built with `ZMod.lift`; `length_maskWord`, `length_maskRow`, `length_maskTags`, `mem_maskTags`, `shiftMaskState_zero`, `subcircle_natCast` and `subcircle_val` are the accompanying lemmas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/CircleWords.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/CircleWords.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FiniteCircle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

@[simp] theorem mem_maskTags (h : ℕ) (p : ℕ → ℕ → ℕ) (l : ℕ) (j : MaskTag h p l) :
    j ∈ maskTags h p l := by
  rcases j with ⟨k,b⟩
  simp only [maskTags, List.mem_flatten, List.mem_ofFn]
  exact ⟨_, ⟨k, rfl⟩, List.mem_ofFn.mpr ⟨b,rfl⟩⟩

@[simp] theorem length_maskTags (h : ℕ) (p : ℕ → ℕ → ℕ) (l : ℕ) :
    (maskTags h p l).length = ∑ k : Fin h, p l k := by
  simp [maskTags, List.length_flatten, List.map_ofFn, List.sum_ofFn]

noncomputable def maskLength (h : ℕ) (p : ℕ → ℕ → ℕ) (R M : ℕ) : ℕ → ℕ
  | 0 => M
  | l+1 => (R*period h p (l+1))*((maskTags h p (l+1)).length*maskLength h p R M l)

@[simp] theorem length_maskWord (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : MaskState h p M l) : (maskWord h p R M l v).length = maskLength h p R M l := by
  induction l with
  | zero =>
    have he := maskWord.eq_1 h p R M v
    dsimp only [MaskState] at v
    dsimp only [MaskAlphabet] at he
    have hh := congrArg (@List.length Bool) he
    simp only [List.length_map, List.bind_eq_flatMap, List.pure_def, ← List.map_eq_flatMap,
      List.length_range] at hh
    exact hh
  | succ l ih =>
    change ((List.range (R*period h p (l+1))).flatMap (fun a =>
      taggedRow (maskTags h p (l+1)) (fun j => maskWord h p R M l
        (shiftMaskState h p M l (v j) (maskGamma h p M (l+1) a j))))).length = _
    rw [length_flatMap_uniform _ _ ((maskTags h p (l+1)).length*maskLength h p R M l)]
    · simp [maskLength]
    · intro a _
      apply length_flatMap_uniform
      intro j _
      simp [ih]

@[simp] theorem shiftMaskState_zero (h : ℕ) (p : ℕ → ℕ → ℕ) (M l : ℕ)
    (v : MaskState h p M l) : shiftMaskState h p M l v 0 = v := by
  induction l with
  | zero => change ZMod M at v; exact add_zero v
  | succ l ih => funext j; exact ih (v j)

def maskRow (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : MaskState h p M (l+1)) (a : ℕ) : List (MaskAlphabet h p (l+1)) :=
  taggedRow (maskTags h p (l+1)) (fun j => maskWord h p R M l
    (shiftMaskState h p M l (v j) (maskGamma h p M (l+1) a j)))

@[simp] theorem length_maskRow (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : MaskState h p M (l+1)) (a : ℕ) :
    (maskRow h p R M l v a).length = (maskTags h p (l+1)).length*maskLength h p R M l := by
  change (MaskTag h p (l+1) → MaskState h p M l) at v
  change (taggedRow (maskTags h p (l+1)) (fun j => maskWord h p R M l
    (shiftMaskState h p M l (v j) (maskGamma h p M (l+1) a j)))).length = _
  unfold taggedRow
  apply length_flatMap_uniform
  intro j _
  rw [List.length_map, length_maskWord]

def halfBit {M : ℕ} (v b : ZMod M) : Bool := decide ((b-v).val < M/2)

noncomputable def halfHamming {M : ℕ} [NeZero M] (v w : ZMod M) : ℕ :=
  (Finset.univ.filter (fun b : ZMod M => halfBit v b ≠ halfBit w b)).card

noncomputable def subcircle {M p : ℕ} (hp : p ∣ M) : ZMod p →+ ZMod M :=
  ZMod.lift p ⟨(AddMonoidHom.mulRight (M/p : ZMod M)).comp (Int.castAddHom _), by
    change ((p : ℤ) : ZMod M) * ((M/p : ℕ) : ZMod M) = 0
    rw [Int.cast_natCast, ← Nat.cast_mul, Nat.mul_div_cancel' hp]
    simp⟩

@[simp] theorem subcircle_natCast {M p : ℕ} (hp : p ∣ M) (a : ℕ) :
    subcircle hp (a : ZMod p) = (M/p : ZMod M)*(a : ZMod M) := by
  have he := ZMod.lift_coe p
    ⟨(AddMonoidHom.mulRight (M/p : ZMod M)).comp (Int.castAddHom _), by
      change ((p : ℤ) : ZMod M) * ((M/p : ℕ) : ZMod M) = 0
      rw [Int.cast_natCast, ← Nat.cast_mul, Nat.mul_div_cancel' hp]
      simp⟩ (a : ℤ)
  simpa [subcircle, Int.castAddHom, mul_comm] using he

@[simp] theorem subcircle_val {M p : ℕ} [NeZero p] (hp : p ∣ M) (a : ZMod p) :
    subcircle hp a = ((M/p*a.val : ℕ) : ZMod M) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  rw [subcircle_natCast]
  simp

namespace PhaseCost
variable {G : Type*} [AddCommGroup G]

end PhaseCost

end FiniteCircle

end OAI


