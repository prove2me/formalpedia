-- Prove2me | Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
-- name    : OAI_Combinatorics_TreeEdit_CircleSeparation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:22:24.757455+00:00
-- url     : https://prove2.me/theorems/524ac68a-53e3-40fd-b057-f68e925054bc
-- title:
--   Quantized circle phases, tree-indexed state vectors and the circle-phase tree word
-- statement:
--   This file builds the words of the circle-phase tree from leaf phases. Let $\mathbb{T}=\mathbb{R}/\mathbb{Z}$ and $[n]=\{0,\dots,n-1\}$. The construction uses the circle-tree data: a labelling $r$ of a pool $I$, a list $j$ of $g$ pool indices, $m=gs$ children per node, configurations $C\in\mathcal{C}_h$ (at a node: a permutation $\sigma$ of $I$, and for each child $i$ a residue and a child configuration $C_i$), the period $P_\sigma$ and the child coefficients $c_i\in\mathbb{N}$ determined by them.
--
--   1. **Representative.** Every $t\in\mathbb{T}$ has a unique representative $\operatorname{rep}(t)\in\mathbb{R}$ with $0\le\operatorname{rep}(t)<1$.
--
--   2. **Bins.** For an integer $R\ge1$, $\operatorname{bin}_R(t)=\lfloor R\operatorname{rep}(t)\rfloor\in[R]$, the index $b$ of the arc $[b/R,(b+1)/R)$ containing $t$.
--
--   3. **State vectors.** For an abelian group $A$, set $\mathcal{S}_0(A)=A$ and $\mathcal{S}_{h+1}(A)=\mathcal{S}_h(A)^{[m]}$: vectors indexed by the leaves of the complete $m$-ary tree of height $h$, i.e. $A^{m^h}$ organised along the tree. It is an abelian group under coordinatewise addition, and finite if $A$ is.
--
--   4. **Diagonal.** $\Delta_h:A\to\mathcal{S}_h(A)$ is the homomorphism placing the same element at every leaf.
--
--   5. **Symbols.** $\Sigma_0=[R]$ and $\Sigma_{h+1}=\{(i,b): i\in[m],\ b\in\Sigma_h\}$. A symbol at height $h$ is thus a root-to-leaf path $(i_1,\dots,i_h)$ followed by a bin index, and $|\Sigma_h|=m^hR$.
--
--   6. **Tree word.** For $C\in\mathcal{C}_h$ and a phase vector $\omega\in\mathcal{S}_h(\mathbb{T})$, the word $X_h(C,\omega)$ of length $(mT)^h$ over $\Sigma_h$ is defined recursively. At height $0$ it is the one-letter word $\operatorname{bin}_R(\omega)$. At height $h+1$, with child configurations $C_i$ and child phase vectors $\omega_i$,
--
--      $$X_{h+1}(C,\omega)=\prod_{a=0}^{T-1}\Bigl(\overline{X_h\bigl(C_0,\ \omega_0+\Delta_h(a c_0/P_\sigma)\bigr)}\ \cdots\ \overline{X_h\bigl(C_{m-1},\ \omega_{m-1}+\Delta_h(a c_{m-1}/P_\sigma)\bigr)}\Bigr),$$
--
--      where the product denotes concatenation in increasing $a$ and the bar tags every symbol of the $i$-th child word with $i$.
--
--   In row $a$ every leaf phase below child $i$ is advanced by $a c_i/P_\sigma$, and the leaves record their quantized phases. Under mild conditions on the parameters, if a shift $t$ is good for $C$ with threshold $\varepsilon=1/R$, then the words of $\omega$ and of $\omega+\Delta_h(t)$ have deficit at least $(mT)^h/128^h$; applied at the root to the half-turn $t=1/2$, this is the separation half of the lower bound for the $\ell_1$ distortion of binary edit distance.
--
--   **Formalization Note** The Lean names are `representative` (via `AddCircle.equivIco 1 0`, with `representative_mem`), `bin R` (requiring `NeZero R`), `State A m h`, `diagonal`, `Symbol m R h` and `word r j T R h C x`, with instances `stateAddCommGroup`, `stateFintype`, `symbolFintype`, and a `Fact (0 < 1)` instance `onePositive` used for the circle. The word length is `FiniteTree.length (g * s) T h`, the interleaving is `Words.cycles`, and the shift $a c_i/P_\sigma$ is the natural number $a c_i$ acting on `point (period r j C.1)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/CircleSeparation.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/CircleSeparation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TreeEdit mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree

namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical

 instance onePositive : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

noncomputable def representative (t : UnitAddCircle) : ℝ := (AddCircle.equivIco 1 0 t).val

lemma representative_mem (t : UnitAddCircle) : 0 ≤ representative t ∧ representative t < 1 := by
  simpa only [representative, Set.mem_Ico, zero_add] using (AddCircle.equivIco 1 0 t).property

noncomputable def bin (R : ℕ) [NeZero R] (t : UnitAddCircle) : Fin R :=
  ⟨⌊(R : ℝ) * representative t⌋₊, (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg R) (representative_mem t).1)).mpr
    (by simpa only [mul_one] using mul_lt_mul_of_pos_left (representative_mem t).2 (by exact_mod_cast NeZero.pos R : (0 : ℝ) < R))⟩

@[reducible] def State (A : Type) (m : ℕ) : ℕ → Type
  | 0 => A
  | h + 1 => Fin m → State A m h

noncomputable instance stateAddCommGroup {A : Type} [AddCommGroup A] (m h : ℕ) : AddCommGroup (State A m h) := by
  induction h with
  | zero => exact inferInstanceAs (AddCommGroup A)
  | succ h ih => exact inferInstanceAs (AddCommGroup (Fin m → State A m h))

noncomputable instance stateFintype {A : Type} [Fintype A] (m h : ℕ) : Fintype (State A m h) := by
  induction h with
  | zero => exact inferInstanceAs (Fintype A)
  | succ h ih => exact inferInstanceAs (Fintype (Fin m → State A m h))

noncomputable def diagonal {A : Type} [AddCommGroup A] {m : ℕ} : (h : ℕ) → A →+ State A m h
  | 0 => AddMonoidHom.id A
  | h + 1 => AddMonoidHom.pi (fun _ : Fin m => diagonal h)

@[reducible] def Symbol (m R : ℕ) : ℕ → Type
  | 0 => Fin R
  | h + 1 => Σ _i : Fin m, Symbol m R h

noncomputable instance symbolFintype (m R h : ℕ) : Fintype (Symbol m R h) := by
  induction h with
  | zero => exact inferInstanceAs (Fintype (Fin R))
  | succ h ih => exact inferInstanceAs (Fintype (Σ _i : Fin m, Symbol m R h))

noncomputable def word {I : Type} {g s L : ℕ} (r : I → ℕ) (j : Fin g → I) (T R : ℕ) [NeZero R] :
    (h : ℕ) → Config I L (g * s) h → State UnitAddCircle (g * s) h → Word (Symbol (g * s) R h) (FiniteTree.length (g * s) T h)
  | 0, _, x => Words.ofFn (fun _ => bin R x)
  | h + 1, C, x => Words.cycles fun a i => word r j T R h (C.2 i).2
      (x i + diagonal (A := UnitAddCircle) (m := g * s) h ((a.val * coefficient r j C.1 (C.2 i).1 i) • point (period r j C.1)))

end TreeEdit.TorusTree

end OAI


