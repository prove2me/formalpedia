-- Prove2me | Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
-- name    : OAI_Combinatorics_FiniteCircle_TreeBranching
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T12:56:55.794325+00:00
-- url     : https://prove2.me/theorems/fbb7d614-6da5-4387-8538-2e89a257e71f
-- title:
--   Tree leaves, cheap phase subgroups, flattening of states and excluded congruences
-- statement:
--   Let $J_1,J_2,\dots$ be sets ($J_l$ indexes the children of a node at height $l$) and $M\in\mathbb{N}$.
--
--   1. **Tree leaves.** $\mathrm{Leaf}_0$ is a one-point set $\{\star\}$ and $\mathrm{Leaf}_{l+1}=J_{l+1}\times\mathrm{Leaf}_l$; thus a leaf of height $l$ is a path $(j_l,j_{l-1},\dots,j_1)$ from the root. It is finite when all $J_r$ are finite.
--   2. **Cheap subgroups.** Let $Z_1,Z_2,\dots$ be abelian groups and $\sigma_l:Z_l\to(\mathbb{Z}/M)^{J_l}$ group homomorphisms. The subgroups $C_l\le(\mathbb{Z}/M)^{\mathrm{Leaf}_l}$ are defined by $C_0=\{0\}$ and: $v\in C_{l+1}$ if there are $c_j\in C_l$ ($j\in J_{l+1}$) and $z\in Z_{l+1}$ with
--   $$
--   v(j,i)=c_j(i)+\sigma_{l+1}(z)_j\qquad\text{for all } j\in J_{l+1},\ i\in\mathrm{Leaf}_l .
--   $$
--   The module checks that each $C_l$ is closed under $0$, addition and negation.
--   3. **From leaf functions to trees.** An integer function $\xi$ on $\mathrm{Leaf}_l$ becomes the frequency tree with those leaf labels: $\xi(\star)$ at height $0$, and $j\mapsto$ (the tree of $i\mapsto\xi(j,i)$) at height $l+1$. Likewise a residue function $v$ on the leaves becomes the nested mask state (children at height $r$ being the mask tags $(k,b)$ with $k<h$ and $b<p(r,k)$) or the nested excluded state (leaves over $J_l=\{0,\dots,m-1\}$) whose level-$0$ residues are the values of $v$.
--   4. **Mask and excluded cheap subgroups.** Given a table $p(l,k)$ with $p(l,k)\mid M$ for all $l,k$, the mask cheap subgroup is $C_l$ for the mask tags, $Z_l=\prod_{k<h}\mathbb{Z}/p(l,k)$ and the mask phase homomorphisms $\sigma_l(z)_{(k',b)}=\sum_{k<h}\iota_{l,k}(z_k)+b\,\iota_{l,k'}(z_{k'})$; the excluded cheap subgroup uses $J_l=\{0,\dots,h-1\}$ and $\sigma_l(z)_i=\sum_{j\ne i}\iota_{l,j}(z_j)$. Here $\iota_{l,k}(a)=(M/p(l,k))\,a$ embeds $\mathbb{Z}/p(l,k)$ in $\mathbb{Z}/M$, and the module notes that $\iota_{l,k}$ sends the class of an integer $a$ to $(M/p(l,k))\,a$.
--   5. **Excluded congruences.** For a frequency tree $t$ over $J_l=\{0,\dots,h-1\}$, with $\Sigma$ the total of the leaf labels: nothing is required at height $0$, and at height $l+1$
--   $$
--   p(l+1,k)\ \Bigm|\ \Sigma(t)-\Sigma(t_k)\qquad\text{for every }k<h,
--   $$
--   together with the excluded congruences for every child $t_j$.
--
--   Shifting the leaf phases of a mask or excluded word by an element of the corresponding cheap subgroup changes the word by comparatively few edits, because such a shift can be absorbed by re-indexing rows. Dually, characters of $(\mathbb{Z}/M)^{\mathrm{Leaf}_l}$ that are trivial on the cheap subgroup have frequency trees satisfying the mask, respectively excluded, congruences. Together these two facts let a Fourier argument isolate the expensive directions of the phase space.
--
--   **Formalization Note** `TreeLeaf J l` is a reducible recursive type (`PUnit` at height $0$) with a `Fintype` instance and a classical `DecidableEq` instance. `treeCheap J Z σ l` is an `AddSubgroup` built by recursion; `treeFrequency`, `flatMaskState` and `flatExcludedState` are the conversions of item 3; `maskCheap` and `excludedCheap` instantiate `treeCheap` (for the excluded one the number of children is named `h`); `subcircle_intCast` is a lemma; `ExcludedCongruences h p l t` is a recursively defined proposition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/TreeBranching.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/TreeBranching.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

@[reducible] def TreeLeaf (J : ℕ → Type) : ℕ → Type
  | 0 => PUnit
  | l+1 => J (l+1) × TreeLeaf J l

instance treeLeafFintype (J : ℕ → Type) [∀ l, Fintype (J l)] (l : ℕ) :
    Fintype (TreeLeaf J l) := by
  induction l with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ l ih => exact @instFintypeProd _ _ inferInstance ih

noncomputable instance treeLeafDecidableEq (J : ℕ → Type) (l : ℕ) :
    DecidableEq (TreeLeaf J l) := Classical.decEq _

noncomputable def treeCheap (J Z : ℕ → Type) [∀ l, AddCommGroup (Z l)] {M : ℕ}
    (σ : ∀ l, Z l →+ (J l → ZMod M)) : (l : ℕ) → AddSubgroup (TreeLeaf J l → ZMod M)
  | 0 => ⊥
  | l+1 => {
    carrier := {v | ∃ c : J (l+1) → TreeLeaf J l → ZMod M,
      (∀ j, c j ∈ treeCheap J Z σ l) ∧ ∃ z : Z (l+1), ∀ j i, v (j,i) = c j i + σ (l+1) z j}
    zero_mem' := by
      refine ⟨0, fun j => (treeCheap J Z σ l).zero_mem, 0, ?_⟩
      intro j i
      change (0:ZMod M) = 0 + σ (l+1) 0 j
      simp
    add_mem' := by
      rintro v w ⟨c,hc,z,hz⟩ ⟨d,hd,u,hu⟩
      refine ⟨c+d, fun j => (treeCheap J Z σ l).add_mem (hc j) (hd j), z+u, ?_⟩
      intro j i
      change v (j,i)+w (j,i) = c j i+d j i+σ (l+1) (z+u) j
      simp only [hz, hu, map_add, Pi.add_apply]
      abel
    neg_mem' := by
      rintro v ⟨c,hc,z,hz⟩
      refine ⟨-c, fun j => (treeCheap J Z σ l).neg_mem (hc j), -z, ?_⟩
      intro j i
      change -v (j,i) = -c j i+σ (l+1) (-z) j
      simp only [hz, map_neg, Pi.neg_apply]
      abel }

noncomputable def treeFrequency (J : ℕ → Type) :
    (l : ℕ) → (TreeLeaf J l → ℤ) → FrequencyTree J l
  | 0, ξ => ξ PUnit.unit
  | l+1, ξ => fun j => treeFrequency J l (fun i => ξ (j,i))

noncomputable def flatMaskState (h : ℕ) (p : ℕ → ℕ → ℕ) (M : ℕ) :
    (l : ℕ) → (TreeLeaf (MaskChildren h p) l → ZMod M) → MaskState h p M l
  | 0, v => v PUnit.unit
  | l+1, v => fun j => flatMaskState h p M l (fun i => v (j,i))

noncomputable def flatExcludedState (m M : ℕ) :
    (l : ℕ) → (TreeLeaf (fun _ => Fin m) l → ZMod M) → ExcludedState m M l
  | 0, v => v PUnit.unit
  | l+1, v => fun j => flatExcludedState m M l (fun i => v (j,i))

@[simp] theorem subcircle_intCast {M p : ℕ} (hp : p ∣ M) (a : ℤ) :
    subcircle hp (a : ZMod p) = (M/p : ZMod M)*(a : ZMod M) := by
  have h := map_zsmul (subcircle hp) a (1 : ZMod p)
  have hc : subcircle hp 1 = (M/p : ZMod M) := by
    simpa only [Nat.cast_one, mul_one] using subcircle_natCast hp 1
  rw [zsmul_eq_mul, mul_one, hc, zsmul_eq_mul] at h
  simpa only [mul_comm] using h

noncomputable def maskCheap (h : ℕ) (p : ℕ → ℕ → ℕ) (M : ℕ)
    (hd : ∀ l (k : Fin h), p l k ∣ M) (l : ℕ) :
    AddSubgroup (TreeLeaf (MaskChildren h p) l → ZMod M) :=
  treeCheap (MaskChildren h p) (MaskResidues h p) (fun l => maskPhaseHom h p M l (hd l)) l

noncomputable def ExcludedCongruences (h : ℕ) (p : ℕ → ℕ → ℕ) :
    (l : ℕ) → FrequencyTree (fun _ => Fin h) l → Prop
  | 0, _ => True
  | l+1, t =>
    (∀ k : Fin h, (p (l+1) k:ℤ) ∣ frequencySum (fun _ => Fin h) (l+1) t -
      frequencySum (fun _ => Fin h) l (t k)) ∧
    ∀ j, ExcludedCongruences h p l (t j)

noncomputable def excludedCheap (h : ℕ) (p : ℕ → ℕ → ℕ) (M : ℕ)
    (hd : ∀ l (k : Fin h), p l k ∣ M) (l : ℕ) :
    AddSubgroup (TreeLeaf (fun _ => Fin h) l → ZMod M) :=
  treeCheap (fun _ => Fin h) (MaskResidues h p) (fun l => excludedPhaseHom h p M l (hd l)) l

end FiniteCircle

end OAI


