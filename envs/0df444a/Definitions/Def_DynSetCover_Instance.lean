-- Prove2me | Definitions.Def_DynSetCover_Instance
-- name    : DynSetCover_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:51.727935+00:00
-- url     : https://prove2.me/theorems/ed66ef55-3a82-415a-92c2-70d6decf6b27
-- title:
--   §1 — weighted set-cover instances, covers, $\mathrm{OPT}_0$, frequency $f$ and $\Delta(A)$
-- statement:
--   An instance of **weighted set cover** consists of a finite universe $U=\{0,\dots,u-1\}$, a fixed family $\mathcal F=\{S_0,\dots,S_{m-1}\}$ of subsets of $U$ whose union is $U$, and a fixed positive **original cost** $c_0(S)>0$ for each $S\in\mathcal F$.
--
--   A subfamily $\mathcal T\subseteq\mathcal F$ **covers** a set $A\subseteq U$ if every element of $A$ lies in some set of $\mathcal T$; its original cost is $\sum_{S\in\mathcal T}c_0(S)$. The optimum
--   $$\mathrm{OPT}_0(A)=\min\Big\{\sum_{S\in\mathcal T}c_0(S)\;:\;\mathcal T\subseteq\mathcal F\text{ covers }A\Big\}$$
--   is attained because $\mathcal F$ itself covers every $A$. The **frequency** $f$ is the largest number of sets containing one element, $I=\sum_{S\in\mathcal F}|S|$ is the size of the set system, and for $A\subseteq U$,
--   $$\Delta(A)=\max_{S\in\mathcal F}|S\cap A|$$
--   is the largest number of elements of $A$ in one input set.
--
--   These are the objects of fully dynamic weighted set cover; every statement of the mission is about them.
--
--   **Formalization Note** The family is indexed by $\{0,\dots,m-1\}$, so two indices may carry the same subset. Costs are real numbers; the word-RAM theorems additionally receive them as rationals (see the protocol definition).
-- source:
--   Paul, Solomon, Weighted Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update Time (STOC 2027 submission, preprint, sha256 a671756b983353737f48798343a4d176654843ba40cd482f54283402087c5cb0), §1, p.1 (PDF 3); OPT0 and Δ_t, p.24 (PDF 26); Remark 1.3, p.3 (PDF 5); I, Theorem 7.5, p.65 (PDF 67)

import Mathlib

namespace DynSetCover

/-- **A weighted set-cover instance** (Paul, Solomon, *Weighted Set Cover with Constant
Worst-Case Recourse* (STOC 2027 submission, sha256 a671756b…), §1, p.1 (PDF 3)): a universe
`U = Fin u`, a fixed family `F = {S s : s ∈ Fin m}` of subsets whose union is `U`, and a fixed
positive cost `c0(S s)` for each set.

**Formalization Note.** Costs are positive reals. The family is indexed, so two indices may
carry the same subset; this is a harmless generalization of "a family". The axiom `covers` is
"whose union is `U`". The word-RAM theorems additionally take the costs as rationals given by a
numerator and a denominator (`RatCosts`, in `DynSetCover.Protocol`). -/
structure Instance where
  /-- number of universe elements; `U = Fin u` -/
  u : ℕ
  /-- number of input sets `m = |F|` -/
  m : ℕ
  /-- the input sets -/
  S : Fin m → Finset (Fin u)
  /-- the original costs `c0` -/
  c0 : Fin m → ℝ
  c0_pos : ∀ s, 0 < c0 s
  /-- the union of the family is the universe -/
  covers : ∀ e : Fin u, ∃ s, e ∈ S s

namespace Instance

variable (inst : Instance)

/-- `T` covers `A`: every element of `A` lies in some set of `T`. -/
noncomputable def Covers (T : Finset (Fin inst.m)) (A : Finset (Fin inst.u)) : Prop :=
  ∀ e ∈ A, ∃ s ∈ T, e ∈ inst.S s

instance (T : Finset (Fin inst.m)) (A : Finset (Fin inst.u)) : Decidable (inst.Covers T A) := by
  unfold Covers; infer_instance

/-- The whole family covers every set of elements (because its union is `U`). -/
theorem covers_univ (A : Finset (Fin inst.u)) : inst.Covers Finset.univ A := fun e _ => by
  obtain ⟨s, hs⟩ := inst.covers e
  exact ⟨s, Finset.mem_univ _, hs⟩

/-- The covers of `A`, a nonempty finite family of subfamilies. -/
noncomputable def coversOf (A : Finset (Fin inst.u)) : Finset (Finset (Fin inst.m)) :=
  Finset.univ.filter (fun T => inst.Covers T A)

theorem coversOf_nonempty (A : Finset (Fin inst.u)) : (inst.coversOf A).Nonempty :=
  ⟨Finset.univ, Finset.mem_filter.2 ⟨Finset.mem_univ _, inst.covers_univ A⟩⟩

/-- The original cost of a subfamily, `Σ_{S∈T} c0(S)`. -/
noncomputable def cost0 (T : Finset (Fin inst.m)) : ℝ := ∑ s ∈ T, inst.c0 s

/-- `OPT0(A)`, the minimum original cost of a subfamily covering `A` (p.24). -/
noncomputable def OPT0 (A : Finset (Fin inst.u)) : ℝ := (inst.coversOf A).inf' (inst.coversOf_nonempty A) inst.cost0

/-- The frequency `f`: the maximum number of sets containing any one element (p.1). -/
noncomputable def freq : ℕ := Finset.univ.sup (fun e : Fin inst.u => (Finset.univ.filter (fun s => e ∈ inst.S s)).card)

/-- `I = Σ_{S∈F} |S|`, the total size of the set system (Theorem 7.5, p.65). -/
noncomputable def totalSize : ℕ := ∑ s, (inst.S s).card

/-- `Δ(A) = max_{S∈F} |S ∩ A|`, the largest number of elements of `A` in one input set
(Remark 1.3, p.3). -/
noncomputable def maxLoad (A : Finset (Fin inst.u)) : ℕ := Finset.univ.sup (fun s => (inst.S s ∩ A).card)

end Instance

end DynSetCover


