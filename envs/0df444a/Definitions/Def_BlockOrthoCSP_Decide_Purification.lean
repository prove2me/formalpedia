-- Prove2me | Definitions.Def_BlockOrthoCSP_Decide_Purification
-- name    : BlockOrthoCSP_Decide_Purification
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:12:25.705716+00:00
-- url     : https://prove2.me/theorems/a8ab276f-ad6f-4c9a-9c03-81b173908a2a
-- title:
--   Generating sets (Definition F.2.2), joint and singleton purification
-- statement:
--   Let $\mu_\infty$ be the roots of unity of $\mathbb C$. For a set $A$ of nonzero complex numbers, a **generating set** (Definition F.2.2) is a tuple $g_1,\dots,g_m$ ($m \ge 0$) with (1) $g_i \in \mathbb Q(A)^\times$; (2) $\prod_i g_i^{k_i} \notin \mu_\infty$ for every nonzero $k \in \mathbb Z^m$; (3) every $a \in A$ has a unique $e(a) \in \mathbb Z^m$ with $a = \vartheta(a)\prod_i g_i^{e_i(a)}$, $\vartheta(a) \in \mu_\infty$.
--
--   With $p_1 = 2, p_2 = 3, \dots$ the primes, put $\varrho(a) = \prod_i p_i^{e_i(a)}$. The **unnormalized purification** of a function replaces each nonzero value $a$ by $\vartheta(a)\varrho(a)$ (zero stays zero); the **normalized purification** multiplies it by the least positive integer $N$ making every $N\varrho(a)$ a positive integer ($N = 1$ for the zero function). For a tuple $(F_1,\dots,F_h)$, $A$ is the set of all nonzero values of the tuple, one generating set is used for the whole tuple and each function is normalized separately (**joint purification**); for one function $G$ this is a **singleton purification** (unnormalized or normalized output).
--
--   **Formalization Note.** `IsJointPurification Fs Ps` holds for the normalized output of any legal generating-set choice; when $A = \emptyset$ every output is the all-zero tuple, as the paper prescribes.
-- source:
--   Liu, Meng, From Block Orthogonality to Decidability in Complex-Weighted Counting CSP, arXiv:2608.14845 (PDF sha256 ad21e5d7…), p. F-8, §F.2.4, Definition F.2.2 and the text after it

import Mathlib
import Definitions.Def_BlockOrthoCSP_Decide_Instance

set_option autoImplicit false

namespace BlockOrthoCSP.Decide

/-- `µ∞`, the group of all roots of unity in `ℂ`: `ξ` with `ξ^N = 1` for some `N ≥ 1` (p. F-6). -/
def muInf : Set ℂ := {ξ | ∃ N : ℕ, 0 < N ∧ ξ ^ N = 1}

/-- Definition F.2.2 (generating set), p. F-8, for the set `A` of nonzero values of a tuple:
`g_1, …, g_m` (`m ≥ 0`) with (1) `g_i ∈ ℚ(A)^×`; (2) `∏ g_i^{k_i} ∉ µ∞` for every nonzero
`k ∈ ℤ^m`; (3) every `a ∈ A` has a unique `e(a) ∈ ℤ^m` with `a = ϑ(a) ∏ g_i^{e_i(a)}`,
`ϑ(a) ∈ µ∞`, i.e. with `a / ∏ g_i^{e_i(a)} ∈ µ∞`. -/
structure IsGeneratingSet (A : Set ℂ) {m : ℕ} (g : Fin m → ℂ) : Prop where
  mem : ∀ i, g i ∈ IntermediateField.adjoin ℚ A
  ne_zero : ∀ i, g i ≠ 0
  indep : ∀ k : Fin m → ℤ, k ≠ 0 → (∏ i, g i ^ k i) ∉ muInf
  exp_unique : ∀ a ∈ A, ∃! e : Fin m → ℤ, a / (∏ i, g i ^ e i) ∈ muInf

open scoped Classical in
/-- The exponent vector `e(a)` of (F.8) (the unique one when `g` is a generating set and
`a ∈ A`). -/
noncomputable def expVec {m : ℕ} (g : Fin m → ℂ) (a : ℂ) : Fin m → ℤ :=
  if h : ∃ e : Fin m → ℤ, a / (∏ i, g i ^ e i) ∈ muInf then h.choose else 0

/-- The root-of-unity factor `ϑ(a) = a / ∏ g_i^{e_i(a)}` of (F.8). -/
noncomputable def rootPart {m : ℕ} (g : Fin m → ℂ) (a : ℂ) : ℂ :=
  a / ∏ i, g i ^ expVec g a i

/-- `ϱ(a) = ∏_{i ∈ [m]} p_i^{e_i(a)} ∈ ℚ_{>0}`, `p_1, p_2, … = 2, 3, …` the primes in order
(`Nat.nth Nat.Prime 0 = 2` is `p_1`), p. F-8. -/
noncomputable def primePart {m : ℕ} (g : Fin m → ℂ) (a : ℂ) : ℚ :=
  ∏ i : Fin m, ((Nat.nth Nat.Prime (i : ℕ) : ℕ) : ℚ) ^ expVec g a i

open scoped Classical in
/-- The purified value: a nonzero `a` becomes `ϑ(a) ϱ(a)`; zero stays zero (p. F-8). -/
noncomputable def purVal {m : ℕ} (g : Fin m → ℂ) (a : ℂ) : ℂ :=
  if a = 0 then 0 else rootPart g a * (primePart g a : ℂ)

/-- The set of nonzero values of a function. -/
def nonzeroValues {α : Type} (G : α → ℂ) : Set ℂ :=
  {a | a ≠ 0 ∧ ∃ x, G x = a}

/-- `N_i`, the least positive integer with `N_i ϱ(a) ∈ ℤ_{>0}` for every nonzero value `a` of the
function (p. F-8); for the zero function every `N ≥ 1` qualifies and the value is `1`. -/
noncomputable def normFactor {α : Type} {m : ℕ} (g : Fin m → ℂ) (G : α → ℂ) : ℕ :=
  sInf {N : ℕ | 0 < N ∧ ∀ x, G x ≠ 0 → ∃ z : ℤ, 0 < z ∧ (N : ℚ) * primePart g (G x) = z}

/-- The unnormalized purification `F̃` of a function with respect to `g` (p. F-8). -/
noncomputable def unnormPur {α : Type} {m : ℕ} (g : Fin m → ℂ) (G : α → ℂ) : α → ℂ :=
  fun x => purVal g (G x)

/-- The normalized purification `F′ = N F̃` (p. F-8). -/
noncomputable def normPur {α : Type} {m : ℕ} (g : Fin m → ℂ) (G : α → ℂ) : α → ℂ :=
  fun x => (normFactor g G : ℂ) * purVal g (G x)

/-- `A(F)`: the set of nonzero values of a finite tuple `(F_1, …, F_h)` (Definition F.2.2). -/
def tupleValues {q h : ℕ} (Fs : Fin h → CFn q) : Set ℂ :=
  {a | a ≠ 0 ∧ ∃ i x, (Fs i).2 x = a}

/-- `Ps` is the normalized joint purification `Pure(F_1, …, F_h)` for some legal generating-set
choice (p. F-8): one generating set `g` for `A(F)`, normalized separately for each function;
arities are kept. If `A(F) = ∅` every output is the all-zero tuple, as the paper prescribes
(the empty generating set `m = 0` is then legal). -/
def IsJointPurification {q h : ℕ} (Fs Ps : Fin h → CFn q) : Prop :=
  ∃ (m : ℕ) (g : Fin m → ℂ), IsGeneratingSet (tupleValues Fs) g ∧
    Ps = fun i => ⟨(Fs i).1, normPur g (Fs i).2⟩

/-- `G′` is a legal singleton purification of `G` (p. F-8): the unnormalized or normalized
output of a legal generating-set choice for the one-element tuple `(G)`. -/
def IsSingletonPurification {α : Type} (G G' : α → ℂ) : Prop :=
  ∃ (m : ℕ) (g : Fin m → ℂ), IsGeneratingSet (nonzeroValues G) g ∧
    (G' = unnormPur g G ∨ G' = normPur g G)

end BlockOrthoCSP.Decide


