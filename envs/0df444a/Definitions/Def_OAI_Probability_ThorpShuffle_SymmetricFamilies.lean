-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_SymmetricFamilies
-- name    : OAI_Probability_ThorpShuffle_SymmetricFamilies
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T04:21:45.019925+00:00
-- url     : https://prove2.me/theorems/434d9fcf-768c-4cf2-896c-3651c8e4ce73
-- title:
--   Specht modules as a Fourier family for the symmetric group $S_n$
-- statement:
--   For a finite set $\alpha$ with $n$ elements and a partition $\lambda=(\lambda_1\ge\lambda_2\ge\cdots)$ of $n$, let $D_\lambda\subseteq\mathbb{N}^2$ be its Young diagram, whose row $r$ consists of the cells $(r,0),\dots,(r,\lambda_{r+1}-1)$, and fix a bijection $t:\alpha\to D_\lambda$. A *tabloid* is a function $f:\alpha\to\mathbb{N}$ of the form $f=\mathrm{row}\circ t\circ g$ with $g$ a permutation of $\alpha$; permutations act on tabloids by $(g\cdot f)(x)=f(g^{-1}x)$, which makes $M^\lambda=\mathbb{C}^{\{\text{tabloids}\}}$, with its standard Hermitian inner product, a permutation representation. The *polytabloid* is $e_t=\sum_{\sigma\in C_t}\operatorname{sgn}(\sigma)\,\delta_{\sigma\cdot f_t}$, where $f_t=\mathrm{row}\circ t$ and $C_t$ is the group of permutations preserving $\mathrm{col}\circ t$, and the *Specht module* $S^\lambda\subseteq M^\lambda$ is the linear span of all translates $g\cdot e_t$, with the restricted action $\pi_\lambda$ and the inherited inner product.
--
--   1. **Unitarity.** For every finite set $\alpha$, every partition $\lambda$ of $|\alpha|$, every permutation $g$ of $\alpha$ and all $v,w\in S^\lambda$: $\langle\pi_\lambda(g)v,\pi_\lambda(g)w\rangle=\langle v,w\rangle$.
--   2. **Regular character identity.** For $n\in\mathbb{N}$ and every $g\in S_n$ (the permutations of $\{0,\dots,n-1\}$), with $\chi_\lambda=\operatorname{tr}\pi_\lambda$,
--   $$\sum_{\lambda\vdash n}\dim(S^\lambda)\,\chi_\lambda(g)=\begin{cases}n!, & g=1,\\ 0, & g\ne 1.\end{cases}$$
--   3. **The symmetric Fourier family.** For each $n$, the Fourier family for $S_n$ indexed by the partitions $\lambda$ of $n$, with spaces $V_\lambda=S^\lambda$ and representations $\pi_\lambda$. Its defining conditions are supplied as follows: each $\pi_\lambda$ is irreducible and $\dim S^\lambda>0$; it is unitary by item 1; $\pi_\lambda\cong\pi_\mu$ implies $\lambda=\mu$; and the regular character identity is item 2.
--
--   Here a Fourier family for a finite group $G$ means a finite family of irreducible, unitary, pairwise inequivalent representations $\rho_i$ on nonzero finite-dimensional complex inner product spaces with $\sum_i\dim(V_i)\chi_{\rho_i}$ equal to the regular character. This packages the classical fact that the Specht modules form a complete system of irreducible unitary representations of $S_n$, so that the general Fourier machinery for finite groups (character kernels, isotypic projectors, joint projectors over products of groups) can be applied to $S_n$ with irreducibles indexed by partitions.
--
--   **Formalization Note** The Lean names are `family_unitary`, `regular_char_fin` and `symmetricFamily n : Thorp.Fourier.Family (Equiv.Perm (Fin n))`, whose index type is `NShape n` (partitions of `Fintype.card (Fin n)`). The Specht module of shape $\lambda$ is `Space p`, built from the fixed bijection `canonicalTableau p`, and $\pi_\lambda$ is `family p`. The private lemmas `ite_eq_left` and `ite_eq_right` are local rewriting helpers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/SymmetricFamilies.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/SymmetricFamilies.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpFirstReciprocal mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins
import Definitions.Def_OAI_Probability_ThorpShuffle_HalfHistories
import Definitions.Def_OAI_Probability_ThorpShuffle_NoiseEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_EnergyDecay
import Definitions.Def_OAI_Probability_ThorpShuffle_MarginalEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalLaw
import Definitions.Def_OAI_Probability_ThorpShuffle_TaggedCompletion
import Definitions.Def_OAI_Probability_ThorpShuffle_Reachability
import Definitions.Def_OAI_Probability_ThorpShuffle_Cyclic
import Definitions.Def_OAI_Probability_ThorpShuffle_Tableaux
import Definitions.Def_OAI_Probability_ThorpShuffle_Specht
import Definitions.Def_OAI_Probability_ThorpShuffle_Polytabloids
import Definitions.Def_OAI_Probability_ThorpShuffle_Irreducibility
import Definitions.Def_OAI_Probability_ThorpShuffle_Classification
import Definitions.Def_OAI_Probability_ThorpShuffle_LinearExtensions
import Definitions.Def_OAI_Probability_ThorpShuffle_ExtensionBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_PartitionBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_DegreeBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_FirstMoment
import Definitions.Def_OAI_Probability_ThorpShuffle_Reynolds
import Definitions.Def_OAI_Probability_ThorpShuffle_FourierFamilies
import Definitions.Def_OAI_Probability_ThorpShuffle_JointProjectors
import Definitions.Def_OAI_Probability_ThorpShuffle_ProductProjectors

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Specht
open scoped Classical
open Thorp.Young

lemma family_unitary {α : Type} [Fintype α] (p : Shape α) (g : Equiv.Perm α) (v w : Space (α:=α) p) :
    ⟪family p g v, family p g w⟫_ℂ = ⟪v, w⟫_ℂ := by
  change ⟪tabloidRep _ _ g v.val, tabloidRep _ _ g w.val⟫_ℂ = ⟪v.val, w.val⟫_ℂ
  exact PermutationSpace.rep_unitary g v.val w.val

lemma regular_char_fin (n : ℕ) (g : Equiv.Perm (Fin n)) :
    ∑ p : NShape n, (Module.finrank ℂ (Space (α:=Fin n) p) : ℂ) * (family (α:=Fin n) p).character g =
      if g = 1 then (Fintype.card (Equiv.Perm (Fin n)) : ℂ) else 0 := by
  have hc : Fintype.card (Equiv.Perm (Fin n)) = Nat.card (Equiv.Perm (Fin n)) := Fintype.card_eq_nat_card
  rw [hc]
  by_cases h : g = 1
  · simpa only [degree, ite_eq_left h] using regular_char g
  · simpa only [degree, ite_eq_right h] using regular_char g

def symmetricFamily (n : ℕ) : Thorp.Fourier.Family (Equiv.Perm (Fin n)) where
  Index := NShape n
  Space := fun p => Space (α:=Fin n) p
  rep := fun p => family (α:=Fin n) p
  positive := by
    intro p
    simpa only [degree] using degree_pos p
  unitary := fun p g v w => family_unitary (α:=Fin n) p g v w
  distinct := fun p q h => family_inequiv (α:=Fin n) p q h
  regular := by
    intro g
    by_cases h : g = 1
    · simpa only [ite_eq_left h] using regular_char_fin n g
    · simpa only [ite_eq_right h] using regular_char_fin n g

end Thorp.Specht

namespace Thorp.Fourier
open scoped Classical

variable {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

end Thorp.Fourier

end

end OAI


