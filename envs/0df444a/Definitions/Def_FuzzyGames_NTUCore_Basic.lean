-- Prove2me | Definitions.Def_FuzzyGames_NTUCore_Basic
-- name    : FuzzyGames_NTUCore_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:48:30.97806+00:00
-- url     : https://prove2.me/theorems/35a3bca7-13f6-4f52-8299-af34936439ee
-- title:
--   Fuzzy games without side payments, their cores, maximum complaint and canonical cooperative equilibria; usual games on a family of coalitions, balances, the fuzzy extension πV
-- statement:
--   This file fixes the vocabulary of §1, §3, §6 (3)–(4) and §7 of Aubin's *Cooperative Fuzzy Games* for games without side payments.
--
--   **Players and fuzzy coalitions.** The players are $N = \{1,\dots,n\}$. A coalition $A \subseteq N$ is identified with its characteristic vector $\tau^A \in \{0,1\}^n$, and $\tau^N = (1,\dots,1)$. A *fuzzy coalition* is $\tau \in [0,1]^n$, with support $A_\tau = \{i : \tau_i > 0\}$. For $\tau \ge 0$ we write $(\tau\cdot c)_i = \tau_i c_i$ and
--   $$\mathbb{R}^\tau = \tau\cdot\mathbb{R}^n,\qquad \mathbb{R}^\tau_+ = \tau\cdot\mathbb{R}^n_+,\qquad \mathring{\mathbb{R}}^\tau_+ = \tau\cdot\mathring{\mathbb{R}}^n_+,$$
--   the vectors vanishing off $A_\tau$ (respectively, nonnegative; strictly positive on $A_\tau$). Further $M^\tau = \{\lambda \in \mathbb{R}^\tau_+ : \sum_{i \in A_\tau} \lambda^i = 1\}$ and $\mathring M^\tau = M^\tau \cap \mathring{\mathbb{R}}^\tau_+$; $M^n = M^{\tau^N}$ is the simplex.
--
--   **Fuzzy games without side payments (§3 (3)).** A map $\tau \mapsto V(\tau)$ such that, for every $\tau \in \mathbb{R}^n_+$:
--
--   1. $V(\tau)$ is a nonempty, closed, convex subset of $\mathbb{R}^\tau$;
--   2. $V(\tau)$ is comprehensive, $V(\tau) = V(\tau) - \mathbb{R}^\tau_+$, and bounded above: $V(\tau) \subseteq C - \mathbb{R}^\tau_+$ for some $C \in \mathbb{R}^\tau$;
--   3. $V$ is positively homogeneous: $V(t\tau) = tV(\tau)$ for every $t > 0$.
--
--   It is *superadditive* (§3 (9), §5 (1)) if $V(\tau) + V(\sigma) \subseteq V(\tau+\sigma)$ for all $\tau, \sigma \in \mathbb{R}^n_+$.
--
--   **Core, complaint, equilibria (§3 (4)–(8)).** The support function is $v(\tau,\lambda) = \sup_{c \in V(\tau)} \sum_i \lambda_i c_i$. The *core* of $V$ is the set of $c$ with
--   $$c \in V(\tau^N)\quad\text{and}\quad \tau\cdot c \notin \mathring V(\tau) = V(\tau) - \mathring{\mathbb{R}}^\tau_+ \ \text{ for every } \tau \in [0,1]^n,\ \tau \neq 0.$$
--   The *maximum complaint* is
--   $$\alpha(c) = \sup_{\tau \in [0,1]^n,\ \tau\neq 0}\ \inf_{\lambda \in M^\tau}\Big[v(\tau,\lambda) - \sum_{i\in N} \lambda^i\tau_i c_i\Big].$$
--   A *weak* (resp. *strong*) *canonical cooperative equilibrium* is a $c \in V(\tau^N)$ for which some $\bar\lambda \in M^n$ (resp. $\bar\lambda \in \mathring M^n$) satisfies $\sum_i \bar\lambda^i \tau_i c_i \ge v(\tau,\bar\lambda)$ for every $\tau \in [0,1]^n$.
--
--   **Usual games without side payments (§7).** $\mathcal{C}$ is a family of nonempty coalitions containing $N$ and every $\{i\}$. A game is a map $A \mapsto V(A)$ with, for every $A \in \mathcal{C}$, $V(A)$ a nonempty, closed, convex, comprehensive, bounded above subset of $\mathbb{R}^A = \mathbb{R}^{\tau^A}$ (§7 (1)). Its *core* is the set of $c \in V(N)$ with $\tau^A\cdot c \notin V(A) - \mathring{\mathbb{R}}^A_+$ for every $A \in \mathcal{C}$ (§7 (2)). With $v(A,\lambda) = \sup_{c\in V(A)} \sum_{i\in A}\lambda^i c_i$, a weak (resp. strong) canonical cooperative equilibrium is a $c \in V(N)$ with some $\bar\lambda \in M^n$ (resp. $\mathring M^n$) such that $\sum_{i\in A}\bar\lambda^i c_i \ge v(A,\bar\lambda)$ for every $A \in \mathcal{C}$ (§7 (3)–(4)).
--
--   **Balances and the fuzzy extension.** $\mathcal{C}(\tau)$ is the set of weights $m \ge 0$ on $\mathcal{C}$ with $\tau_i = \sum_{A \ni i} m(A)$ for every $i$ (§6 (3)–(4)). The fuzzy extension of $V$ is
--   $$\pi V(\tau) = \bigcup_{m\in\mathcal{C}(\tau)} \sum_{A\in\mathcal{C}} m(A)\,V(A)\qquad(\S 7\ (5)),$$
--   and $\pi v(\tau,\lambda) = \sup_{m\in\mathcal{C}(\tau)} \sum_{A\in\mathcal{C}} m(A)\,v(A,\lambda)$. The game is *balanced* if $V(N) = \pi V(\tau^N)$ (§7 (8)).
--
--   These objects are shared by every statement of the mission, from Proposition 3.1 to Theorem 7.1.
--
--   **Formalization Note.** Players are `Fin n`; vectors are `Fin n → ℝ`, ordered coordinatewise. $\mathbb{R}^\tau$ is encoded as "vanishes where $\tau_i = 0$", which equals $\tau\cdot\mathbb{R}^n$ for $\tau \ge 0$, and the dual $\mathbb{R}^{\tau*}$ is identified with $\mathbb{R}^\tau$. The paper defines $V$ on $[0,1]^n$ and extends it to $\mathbb{R}^n_+$ by homogeneity; we state the axioms directly on the orthant $\tau \ge 0$, and values off the orthant are unconstrained and never used. The core, the complaint and the equilibria are defined for an arbitrary set-valued map, so that they apply to $\pi V$ before it is shown to be a fuzzy game. Support functions are suprema in `EReal` (so $+\infty$ and, for the empty set, $-\infty$ are kept, never replaced by $0$); $\pi v$ multiplies the real weights $m(A)$ into `EReal`. The sup in $\alpha$ is taken over $\tau \neq 0$: the paper writes $\tau \in [0,1]^n$, but $M^0 = \emptyset$ makes the inner infimum $+\infty$ at $\tau = 0$, which would make $\alpha \equiv +\infty$ and contradict Proposition 3.1; $\tau\neq 0$ matches the core's "$\forall \tau \neq 0$". Comprehensiveness is the paper's equality $V = V - \mathbb{R}^\tau_+$ with Minkowski difference. $\mathcal{C}$ excludes $\emptyset$, so "$\forall A \neq \emptyset$" in §7 (2)–(3) ranges over $\mathcal{C}$. Sums and scalings of sets are Mathlib's pointwise operations; $0\cdot S = \{0\}$ for nonempty $S$. Weights $m$ are functions on all coalitions vanishing off $\mathcal{C}$.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), §1, p. 2; §3 (1)–(9), pp. 3–5; §6 (3)–(4), p. 8; §7 (1)–(5), (8), (10)–(11), pp. 8–9

import Mathlib

namespace FuzzyGames.NTUCore

open Set Finset Pointwise

variable {n : ℕ}

/-- The cube `[0,1]^n` of fuzzy coalitions (§1, p. 2), in the coordinatewise order. -/
def cube (n : ℕ) : Set (Fin n → ℝ) := Set.Icc 0 1

/-- The nonnegative orthant `ℝ^n_+`, the domain of a fuzzy game after its extension by
positive homogeneity (§3, p. 3). -/
def orthant (n : ℕ) : Set (Fin n → ℝ) := Set.Ici 0

/-- `τ^A`, the characteristic vector of the coalition `A ⊆ N` (§1, p. 2).
`τ^N` is `coal Finset.univ`, the vector `(1, …, 1)`. -/
def coal (A : Finset (Fin n)) : Fin n → ℝ := fun i => if i ∈ A then 1 else 0

/-- The coordinatewise product `τ · c`, `(τ · c)_i = τ_i c_i` (§3 (1)). -/
def tmul (τ c : Fin n → ℝ) : Fin n → ℝ := fun i => τ i * c i

/-- `ℝ^τ = τ · ℝ^n` (§3 (2)): for `τ ≥ 0`, the vectors vanishing off the support
`A_τ = {i | τ_i > 0}`. -/
def Rtau (τ : Fin n → ℝ) : Set (Fin n → ℝ) := {c | ∀ i, τ i = 0 → c i = 0}

/-- `ℝ^τ_+ = τ · ℝ^n_+` (§3 (2)): nonnegative vectors vanishing off `A_τ`. -/
def RtauNonneg (τ : Fin n → ℝ) : Set (Fin n → ℝ) := {c | c ∈ Rtau τ ∧ ∀ i, 0 ≤ c i}

/-- `ℝ̊^τ_+ = τ · ℝ̊^n_+` (§3 (2)): vectors strictly positive on `A_τ` and zero off it. -/
def RtauPos (τ : Fin n → ℝ) : Set (Fin n → ℝ) := {c | c ∈ Rtau τ ∧ ∀ i, 0 < τ i → 0 < c i}

/-- The support function `λ ↦ sup_{c ∈ W} Σ_i λ_i c_i` of a set `W ⊆ ℝ^n`, valued in `EReal`
(it is `+∞` when the sup is unbounded and `⊥ = -∞` when `W = ∅`). -/
noncomputable def supportFn (W : Set (Fin n → ℝ)) (l : Fin n → ℝ) : EReal :=
  ⨆ c ∈ W, ((∑ i, l i * c i : ℝ) : EReal)

/-- `M^τ = {λ ∈ ℝ^τ_+ | Σ_{i ∈ A_τ} λ^i = 1}` (§3 (6)). `M^n` is `simplexOn (coal univ)`. -/
def simplexOn (τ : Fin n → ℝ) : Set (Fin n → ℝ) := {l | l ∈ RtauNonneg τ ∧ ∑ i, l i = 1}

/-- `M̊^τ = M^τ ∩ ℝ̊^τ_+` (§3 (6)). `M̊^n` is `simplexOnPos (coal univ)`. -/
def simplexOnPos (τ : Fin n → ℝ) : Set (Fin n → ℝ) := simplexOn τ ∩ RtauPos τ

/-! ### Fuzzy games without side payments (§3) -/

/-- A **fuzzy game without side payments** (§3 (3)), encoded on the orthant `τ ≥ 0` to which the
paper extends it by positive homogeneity: for every `τ ≥ 0`, `V(τ)` is a nonempty, closed, convex
subset of `ℝ^τ`, comprehensive (`V(τ) = V(τ) − ℝ^τ_+`) and bounded above
(`V(τ) ⊆ C − ℝ^τ_+` for some `C ∈ ℝ^τ`); and `V(tτ) = t V(τ)` for all `t > 0`. -/
structure IsNTUFuzzyGame (V : (Fin n → ℝ) → Set (Fin n → ℝ)) : Prop where
  subset_Rtau : ∀ τ ∈ orthant n, V τ ⊆ Rtau τ
  nonempty : ∀ τ ∈ orthant n, (V τ).Nonempty
  isClosed : ∀ τ ∈ orthant n, IsClosed (V τ)
  convex : ∀ τ ∈ orthant n, Convex ℝ (V τ)
  comprehensive : ∀ τ ∈ orthant n, V τ - RtauNonneg τ = V τ
  bddAbove : ∀ τ ∈ orthant n, ∃ C ∈ Rtau τ, V τ ⊆ {C} - RtauNonneg τ
  homogeneous : ∀ t : ℝ, 0 < t → ∀ τ ∈ orthant n, V (t • τ) = t • V τ

/-- Superadditivity (§3 (9) = §5 (1)): `V(τ) + V(σ) ⊆ V(τ + σ)` for all `τ, σ ∈ ℝ^n_+`. -/
def Superadditive (V : (Fin n → ℝ) → Set (Fin n → ℝ)) : Prop :=
  ∀ τ ∈ orthant n, ∀ σ ∈ orthant n, V τ + V σ ⊆ V (τ + σ)

/-- The **core of a fuzzy game without side payments** (§3 (4)), for any set-valued map `W`:
`c ∈ W(τ^N)` and no fuzzy coalition `τ ≠ 0` improves upon `c`, i.e.
`τ · c ∉ W(τ) − ℝ̊^τ_+`. -/
def fuzzyCore (W : (Fin n → ℝ) → Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {c | c ∈ W (coal Finset.univ) ∧
    ∀ τ ∈ cube n, τ ≠ 0 → tmul τ c ∉ W τ - RtauPos τ}

/-- The complaint `inf_{λ ∈ M^τ} [v(τ, λ) − Σ_i λ^i τ_i c_i]` of the fuzzy coalition `τ` against
`c` (§3, p. 4), where `v(τ, λ)` is the support function of `W(τ)` (§3 (5)). -/
noncomputable def complaint (W : (Fin n → ℝ) → Set (Fin n → ℝ)) (τ c : Fin n → ℝ) : EReal :=
  ⨅ l ∈ simplexOn τ, (supportFn (W τ) l - ((∑ i, l i * τ i * c i : ℝ) : EReal))

/-- The maximum complaint function `α` (§3 (7)): the supremum of the complaints over the
fuzzy coalitions `τ ∈ [0,1]^n` with `τ ≠ 0`. -/
noncomputable def maxComplaint (W : (Fin n → ℝ) → Set (Fin n → ℝ)) (c : Fin n → ℝ) : EReal :=
  ⨆ τ ∈ {τ : Fin n → ℝ | τ ∈ cube n ∧ τ ≠ 0}, complaint W τ c

/-- Weak canonical cooperative equilibria of a fuzzy game (§3 (8)): `c ∈ W(τ^N)` and some
`λ̄ ∈ M^n` satisfies `v(τ, λ̄) ≤ Σ_i λ̄^i τ_i c_i` for every `τ ∈ [0,1]^n`. -/
def weakCCE (W : (Fin n → ℝ) → Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {c | c ∈ W (coal Finset.univ) ∧ ∃ l ∈ simplexOn (coal (Finset.univ : Finset (Fin n))),
    ∀ τ ∈ cube n, supportFn (W τ) l ≤ ((∑ i, l i * τ i * c i : ℝ) : EReal)}

/-- Strong canonical cooperative equilibria of a fuzzy game (§3, p. 5): as `weakCCE`, with
`λ̄ ∈ M̊^n = M^n ∩ ℝ̊^n_+`. -/
def strongCCE (W : (Fin n → ℝ) → Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {c | c ∈ W (coal Finset.univ) ∧ ∃ l ∈ simplexOnPos (coal (Finset.univ : Finset (Fin n))),
    ∀ τ ∈ cube n, supportFn (W τ) l ≤ ((∑ i, l i * τ i * c i : ℝ) : EReal)}

/-! ### Usual games without side payments on a family of coalitions (§6 (3)–(4), §7) -/

/-- The family `𝒞` of admissible coalitions (§1): it contains `N` and every singleton `{i}`.
The empty coalition is excluded (the paper only ever uses `A ≠ ∅`). -/
structure CoalFamily (n : ℕ) where
  C : Finset (Finset (Fin n))
  univ_mem : (Finset.univ : Finset (Fin n)) ∈ C
  singleton_mem : ∀ i, ({i} : Finset (Fin n)) ∈ C
  empty_not_mem : (∅ : Finset (Fin n)) ∉ C

/-- The balances `𝒞(τ)` of `τ` (§6 (3)–(4)): nonnegative weights `m(A)`, vanishing off `𝒞`, with
`τ_i = Σ_{A ∈ 𝒞, A ∋ i} m(A)` for every player `i`. -/
def balances (𝒞 : CoalFamily n) (τ : Fin n → ℝ) : Set (Finset (Fin n) → ℝ) :=
  {m | (∀ A, 0 ≤ m A) ∧ (∀ A, A ∉ 𝒞.C → m A = 0) ∧
    ∀ i, ∑ A ∈ 𝒞.C.filter (fun A => i ∈ A), m A = τ i}

/-- A **game without side payments** on `𝒞` (§7 (1)): for every `A ∈ 𝒞`, `V(A)` is a nonempty,
closed, convex subset of `ℝ^A = ℝ^{τ^A}`, comprehensive (`V(A) = V(A) − ℝ^A_+`) and bounded above
(`V(A) ⊆ C − ℝ^A_+` for some `C ∈ ℝ^A`). -/
structure IsNTUGame (𝒞 : CoalFamily n) (V : Finset (Fin n) → Set (Fin n → ℝ)) : Prop where
  subset_Rtau : ∀ A ∈ 𝒞.C, V A ⊆ Rtau (coal A)
  nonempty : ∀ A ∈ 𝒞.C, (V A).Nonempty
  isClosed : ∀ A ∈ 𝒞.C, IsClosed (V A)
  convex : ∀ A ∈ 𝒞.C, Convex ℝ (V A)
  comprehensive : ∀ A ∈ 𝒞.C, V A - RtauNonneg (coal A) = V A
  bddAbove : ∀ A ∈ 𝒞.C, ∃ C ∈ Rtau (coal A), V A ⊆ {C} - RtauNonneg (coal A)

/-- The core of a game without side payments (§7 (2)): `c ∈ V(N)` and
`τ^A · c ∉ V(A) − ℝ̊^A_+` for every `A ∈ 𝒞`. -/
def ntuCore (𝒞 : CoalFamily n) (V : Finset (Fin n) → Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {c | c ∈ V Finset.univ ∧ ∀ A ∈ 𝒞.C, tmul (coal A) c ∉ V A - RtauPos (coal A)}

/-- The support function `v(A, λ) = sup_{c ∈ V(A)} Σ_{i ∈ A} λ^i c_i` of `V(A)` (§7 (4)),
valued in `EReal`. -/
noncomputable def coalSupport (V : Finset (Fin n) → Set (Fin n → ℝ)) (A : Finset (Fin n))
    (l : Fin n → ℝ) : EReal :=
  ⨆ c ∈ V A, ((∑ i ∈ A, l i * c i : ℝ) : EReal)

/-- Weak canonical cooperative equilibria of a game without side payments (§7 (3)):
`c ∈ V(N)` and some `λ̄ ∈ M^n` satisfies `v(A, λ̄) ≤ Σ_{i ∈ A} λ̄^i c_i` for every `A ∈ 𝒞`. -/
def ntuWeakCCE (𝒞 : CoalFamily n) (V : Finset (Fin n) → Set (Fin n → ℝ)) :
    Set (Fin n → ℝ) :=
  {c | c ∈ V Finset.univ ∧ ∃ l ∈ simplexOn (coal (Finset.univ : Finset (Fin n))),
    ∀ A ∈ 𝒞.C, coalSupport V A l ≤ ((∑ i ∈ A, l i * c i : ℝ) : EReal)}

/-- Strong canonical cooperative equilibria of a game without side payments (§7 (3)): as
`ntuWeakCCE`, with `λ̄ ∈ M̊^n`. -/
def ntuStrongCCE (𝒞 : CoalFamily n) (V : Finset (Fin n) → Set (Fin n → ℝ)) :
    Set (Fin n → ℝ) :=
  {c | c ∈ V Finset.univ ∧ ∃ l ∈ simplexOnPos (coal (Finset.univ : Finset (Fin n))),
    ∀ A ∈ 𝒞.C, coalSupport V A l ≤ ((∑ i ∈ A, l i * c i : ℝ) : EReal)}

/-- The fuzzy extension `πV(τ) = ⋃_{m ∈ 𝒞(τ)} Σ_{A ∈ 𝒞} m(A) V(A)` (§7 (5)), with Minkowski
sums and scalings of sets. -/
def piV (𝒞 : CoalFamily n) (V : Finset (Fin n) → Set (Fin n → ℝ)) (τ : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  ⋃ m ∈ balances 𝒞 τ, ∑ A ∈ 𝒞.C, m A • V A

/-- `πv(τ, λ) = sup_{m ∈ 𝒞(τ)} Σ_{A ∈ 𝒞} m(A) v(A, λ)` (§7 (10)–(11)), valued in `EReal`. -/
noncomputable def piv (𝒞 : CoalFamily n) (V : Finset (Fin n) → Set (Fin n → ℝ))
    (τ l : Fin n → ℝ) : EReal :=
  ⨆ m ∈ balances 𝒞 τ, ∑ A ∈ 𝒞.C, ((m A : ℝ) : EReal) * coalSupport V A l

/-- A game without side payments is **balanced** (§7 (8)) if `V(N) = πV(τ^N)`. -/
def IsBalanced (𝒞 : CoalFamily n) (V : Finset (Fin n) → Set (Fin n → ℝ)) : Prop :=
  V Finset.univ = piV 𝒞 V (coal Finset.univ)

end FuzzyGames.NTUCore


