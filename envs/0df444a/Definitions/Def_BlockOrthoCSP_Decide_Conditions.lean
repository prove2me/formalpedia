-- Prove2me | Definitions.Def_BlockOrthoCSP_Decide_Conditions
-- name    : BlockOrthoCSP_Decide_Conditions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:13:04.775425+00:00
-- url     : https://prove2.me/theorems/3ed2964d-2554-4bd2-a6a8-6d76b55a9b72
-- title:
--   The conditions $\mathrm{BO}$ (Definition F.2.3), $\mathrm{TP}$, $\mathrm{Mal}$ (Definition F.2.4) and $\mathrm{CC}$
-- statement:
--   Let $\mathcal F$ be a constraint language with generated family $W_{\mathcal F}$.
--
--   - $\mathrm{BO}(\mathcal F)$ (Definition F.2.3): for every nonempty finite tuple $(F_1,\dots,F_h)$ of pairwise distinct members of $W_{\mathcal F}$ and every joint purification $(F_1',\dots,F_h')$ of it, $F_i'$ is block-orthogonal whenever $\operatorname{arity}(F_i) \ge 2$.
--   - $\mathrm{TP}(\mathcal F)$: every member of $W_{\mathcal F}$ of arity at least two has a type-partition map.
--   - $\mathrm{Mal}(\mathcal F)$: some Mal'tsev operation $\varphi : D^3 \to D$ ($\varphi(a,b,b) = \varphi(b,b,a) = a$) preserves every relation of $\Lambda_{\mathcal F} = \{\Phi_F : F \in W_{\mathcal F}\} \cup \{\Omega_F : F \in W_{\mathcal F},\ \operatorname{arity}(F) \ge 2\}$.
--   - $$\mathrm{CC}(\mathcal F) = \mathrm{BO}(\mathcal F) \wedge \mathrm{TP}(\mathcal F) \wedge \mathrm{Mal}(\mathcal F).$$
--
--   Also defined: a function **has a block-orthogonal singleton purification** (`HasBOPurification`), and the **singleton Block Orthogonality condition** (`SingletonBO`): every member of $W_{\mathcal F}$ of arity at least two has one.
--
--   **Formalization Note.** Preservation and the Mal'tsev identities are the published `ConsModCount_Polymorphism` notions. $\mathrm{BO}$ is required for every legal generating-set choice; Lemma F.3.1 shows the paper's fixed choice gives the same condition.
-- source:
--   Liu, Meng, From Block Orthogonality to Decidability in Complex-Weighted Counting CSP, arXiv:2608.14845 (PDF sha256 ad21e5d7…), pp. F-1, F-8–F-9, Definitions F.2.3 and F.2.4; p. F-13 (singleton condition)

import Mathlib
import Definitions.Def_ConsModCount_Polymorphism
import Definitions.Def_BlockOrthoCSP_Decide_Instance
import Definitions.Def_BlockOrthoCSP_Decide_Rows
import Definitions.Def_BlockOrthoCSP_Decide_Purification

set_option autoImplicit false

namespace BlockOrthoCSP.Decide

/-- Definition F.2.3 (global Block Orthogonality condition `BO(F)`), p. F-8: for every nonempty
finite tuple `(F_1, …, F_h)` of pairwise distinct members of `W_F` and its joint purification
`(F′_1, …, F′_h)`, `F′_i` is block-orthogonal for every `i` with `arity(F_i) ≥ 2`.
Reading: the condition is required for every legal generating-set choice (Lemma F.3.1 shows the
outcome does not depend on the choice). Arity `≥ 2` is written `arity = j + 1` with `j ≥ 1`. -/
def BO {q : ℕ} (F : Finset (CFn q)) : Prop :=
  ∀ (h : ℕ) (Fs : Fin h → CFn q), 1 ≤ h → Function.Injective Fs → (∀ i, Fs i ∈ W F) →
    ∀ Ps : Fin h → CFn q, IsJointPurification Fs Ps →
      ∀ (i : Fin h) (j : ℕ) (G' : (Fin (j + 1) → Fin q) → ℂ), 1 ≤ j → Ps i = ⟨j + 1, G'⟩ →
        IsBlockOrthogonal G'

/-- Definition F.2.4, Type Partition condition `TP(F)`, p. F-9: every member of `W_F` of arity
at least two has a type-partition map. -/
def TP {q : ℕ} (F : Finset (CFn q)) : Prop :=
  ∀ (j : ℕ) (G : (Fin (j + 1) → Fin q) → ℂ), 1 ≤ j → (⟨j + 1, G⟩ : CFn q) ∈ W F →
    IsTypePartition G

/-- Definition F.2.4, Mal'tsev polymorphism condition `Mal(F)`, p. F-9: one Mal'tsev operation
`φ : D^3 → D` preserves every relation of
`Λ_F = {Φ_F : F ∈ W_F} ∪ {Ω_F : F ∈ W_F, arity(F) ≥ 2}`. `Preserves`, `ternary` and
`IsMaltsev` are the published `ConsModCount_Polymorphism` notions (coordinatewise
preservation; `φ(a, b, b) = φ(b, b, a) = a`). -/
def Mal {q : ℕ} (F : Finset (CFn q)) : Prop :=
  ∃ φ : Fin q → Fin q → Fin q → Fin q, ConsModCount.IsMaltsev φ ∧
    (∀ G ∈ W F, ConsModCount.Preserves (ConsModCount.ternary φ) (Phi G.2)) ∧
    ∀ (j : ℕ) (G : (Fin (j + 1) → Fin q) → ℂ), 1 ≤ j → (⟨j + 1, G⟩ : CFn q) ∈ W F →
      ConsModCount.Preserves (ConsModCount.ternary φ) (Omega G)

/-- `G` has a block-orthogonal singleton purification (Corollary F.3.2, p. F-13). -/
def HasBOPurification {q j : ℕ} (G : (Fin (j + 1) → Fin q) → ℂ) : Prop :=
  ∃ G' : (Fin (j + 1) → Fin q) → ℂ, IsSingletonPurification G G' ∧ IsBlockOrthogonal G'

/-- The singleton Block Orthogonality condition on `W_F` (pp. F-13): every member of `W_F` of
arity at least two has a block-orthogonal singleton purification. -/
def SingletonBO {q : ℕ} (F : Finset (CFn q)) : Prop :=
  ∀ (j : ℕ) (G : (Fin (j + 1) → Fin q) → ℂ), 1 ≤ j → (⟨j + 1, G⟩ : CFn q) ∈ W F →
    HasBOPurification G

/-- Cai and Chen's tractability criterion `CC(F) = BO(F) ∧ TP(F) ∧ Mal(F)`, p. F-1. -/
def CC {q : ℕ} (F : Finset (CFn q)) : Prop :=
  BO F ∧ TP F ∧ Mal F

end BlockOrthoCSP.Decide


