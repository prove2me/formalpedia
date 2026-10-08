-- Prove2me | Definitions.Def_ErschlerZheng_Construction
-- name    : ErschlerZheng_Construction
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-05T21:39:46.516924+00:00
-- url     : https://prove2.me/theorems/439059ab-5e20-432d-a1eb-a56400b83974
-- title:
--   Erschler–Zheng §7.2 — the sequence g_n, the index sets W^n_k and V^j_k, the conjugates 𝔠^v_j and g̃^v_j, the sets 𝔉_{j,n}, the uniformised quasi-cubic measures υ_n and the measure μ_β
-- statement:
--   Definitions from §7.2 of Erschler and Zheng, *Growth of periodic Grigorchuk groups*, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (pp. 35–42 of arXiv:1802.09077v2), built on the Grigorchuk bundle (`evalWord`, `zetaWord`, `zetaHat`, `gen`, `iota`, `frM`, `frI`, `commonPrefixLength`, `grigorchuk`, `genSet`) and on `uniformMeasure` of the Walks bundle. Group elements are `Garrido.BinaryTreeAut`, acting on the right as in the Grigorchuk bundle, so a product $g h$ of the paper is the Lean product `g * h`. Digits: `false` is $0$ and `true` is $1$; the paper's digit $v_i$ of a vertex is Lean's `v[i - 1]`. Commutators are Mathlib's $⁅x, y⁆ = x y x^{-1} y^{-1}$; every commutator below is of $a$ and $b_{\mathfrak s^m\omega}$, two involutions by construction (`Garrido.grigA` and `gen` are built as involutive permutations, through `Garrido.grigAFun_involutive` and `ErschlerZheng.genFun_involutive`), for which this is $xyxy$ under either convention.
--
--   - `seqG ω n` is $g_n$ of (7.1), p. 35: “First take the sequence of words obtained by substitutions: (7.1) $g_n = \zeta_{\omega_0} \circ \ldots \zeta_{\omega_{n-1}}(ab_{\mathfrak s^n\omega})$ if $\omega_{n-1} \neq \mathbf 2$, $\zeta_{\omega_0} \circ \ldots \zeta_{\omega_{n-1}}(ac_{\mathfrak s^n\omega})$ if $\omega_{n-1} = \mathbf 2$.” The substitutions are applied to the one-letter word $ab$ or $ac$ over $\{ab, ac, ad\}$ (`zetaWord`), innermost $\zeta_{\omega_{n-1}}$ first, and the resulting word is evaluated in $G_\omega$ (`evalWord ω 0`). Only $n \ge 1$ is used; at $n = 0$ the test reads $\omega_0$, a junk value.
--   - `wSet D ω n k` is $\mathsf W^n_k$ of (7.2), p. 37: “For $k, n \in \mathbb N$ both divisible by $D$, define the set $\mathsf W^n_k$ of vertices of depth $k$ such that $u_i = 1$ except for those $i$ with $n + i \in I_\omega$, (7.2) $\mathsf W^n_k := \{u \in \mathsf L_k : u = u_1 \ldots u_k,\ u_i = 1 \text{ if } n + i \notin I_\omega\}$.” $I_\omega$ is `frI D ω` of Notation 7.1. The definition accepts every $n$ and $k$.
--   - `ellIndex D k j` and `vSet D ω j k` are $\ell(k, j)$ and $\mathsf V^j_k$ of (7.3), p. 37: “Given an integer $j$, denote by $\bar j$ the residue of $j$ mod $D$, $\bar j \in \{0, \ldots, D-1\}$.” and “Let $k$ be an integer divisible by $D$, write $\ell(k, j) = \frac1D(j + D - \bar j + k)$ and define $\mathsf V^j_k$ the collection of vertices (7.3) $\mathsf V^j_k := \{1^{D-\bar j}u1^{m_{\ell(j,k)}+2}0 : u \in \mathsf W^{j+D-\bar j}_k\}$, where $m_\ell$ is defined in Notation 7.1, $m_\ell \in \{0, \ldots, D-3\}$.” The paper writes $\ell(k, j)$ in the definition and $m_{\ell(j,k)}$ in (7.3); both are the same index. `ellIndex` divides in $\mathbb N$, which is exact precisely when $D$ divides $k$ (`ErschlerZheng.mul_ellIndex_eq_iff_dvd`); $m_\ell$ is `frM D ω ℓ`. The definition accepts every $k$.
--   - `hElt ω j v i` and `hProd ω j v` are $h^v_i$ of (7.4) and the product $h^v_1 h^v_2 \ldots h^v_{k'}$, $k' = |v|$, p. 38: “Given a vertex $v = v_1 \ldots v_{k'} \in \mathsf V^j_k$, where $k' = D - \bar j + k + m_{\ell(j,k)} + 3$ denotes the length of $v$, take the following sequence of elements in $G_j = G_{\mathfrak s^j\omega}$: (7.4) $h^v_i := id$ if $v_i = 1$, $\iota([b_{\mathfrak s^{j+i-2}\omega}, a], v_1 \ldots v_{i-2})$ if $v_i = 0$.” Here $\iota$ is `iota` and $b_{\mathfrak s^m\omega}$ is `gen (shiftSeq ω m) .b`. For $D \ge 1$ (Assumption $(\mathrm{Fr}(D))$ asks for some $m$ with $m + 3 \le D$), a vertex of $\mathsf V^j_k$ begins with $1^{D - \bar j}$, at least one digit $1$, so $h^v_1 = id$ and the value at $i = 1$ with $v_1 = 0$, where $i - 2$ is truncated to $0$, never arises; a digit beyond the end of $v$ is read as $1$.
--   - `cElt ω j v` is $\mathfrak c^v_j$ of (7.5), p. 38: “For each $v \in \mathsf V^j_k$, take the conjugation of $c_{\mathfrak s^j\omega}$ in $G_j$ (7.5) $\mathfrak c^v_j := (h^v_1 h^v_2 \ldots h^v_{k'})^{-1} c_{\mathfrak s^j\omega} (h^v_1 h^v_2 \ldots h^v_{k'})$.”
--   - `gTilde ω j v` is $\tilde g^v_j$ of (7.6), p. 39: “Next we apply the substitutions $\zeta_x$ to $a\mathfrak c^v_j$, which is an element in $G_j$, to obtain an element in $G_\omega$. Given $j$ and a vertex $v \in \mathsf V^j_k$ where $D|k$, define (7.6) $\tilde g^v_j := \zeta_{\omega_0} \circ \ldots \circ \zeta_{\omega_{j-1}}(a\mathfrak c^v_j)$.” Each $\zeta_{\omega_i}$ applied to a group element is `zetaHat ω i` of the Grigorchuk bundle, innermost $\zeta_{\omega_{j-1}}$ first; `zetaHat` evaluates the substitution on a chosen representing word, a word in the free group on $ab, ac, ad$, and takes the value $1$ at an element with no such word. That $a\mathfrak c^v_j$ has a representing word, the first claim of Lemma 7.9 (“The element $\tilde g^v_j$ is well defined (the substitutions $\zeta_{\omega_i}$'s can be applied).”), is part of the milestone `ErschlerZheng.exists_evalFree_eq_and_gTilde_mem_levelStab_and_sec_mem`.
--   - `IsAdmissibleSeq D k` is the standing assumption of p. 40: “Let $(k_n)$ be a sequence of increasing positive integers divisible by $D$ to be determined later, $k_n \ll n$. In what follows $n$ is always an integer divisible by $D$.” It says that $k$ is non-decreasing and that $k_n$ is positive and divisible by $D$ for every $n \ge 1$ divisible by $D$, the only $n$ used. “Increasing” is read as non-decreasing, since the choice $k_n = A\lfloor\log_2 n\rfloor$ of p. 42 has $k_2 = k_3 = A$ (`ErschlerZheng.isAdmissibleSeq_kLog_and_kLog_two_eq_and_kLog_three_eq`). The informal “$k_n \ll n$” is not part of the predicate; a statement that needs a bound on $k_n$ assumes it.
--   - `kLog A n` is $k_n = A\lfloor\log_2 n\rfloor$, p. 42: “The goal of this subsection is to show that with some appropriate choices of $\beta$ and $A$, the measure $\mu_\beta$ defined in (7.11) with $k_n = A\lfloor\log_2 n\rfloor$ has non-trivial Poisson boundary.” $\lfloor\log_2 n\rfloor$ is `Nat.log 2 n`, which is $0$ at $n = 0$.
--   - `fSet D ω k j n` is $\mathfrak F_{j,n}$ of (7.7), p. 40: “For each $j \in \{1, \ldots, n\}$, take the following sets $\mathfrak F_{j,n}$ of group elements in $G_\omega$, • For an index $j$ such that $\omega_{j-1} = \mathbf 2$ and $n - k_n < j \leqslant n$, define $\mathfrak F_{j,n}$ to be the following set of elements $\tilde g^v_j = \zeta_{\omega_0} \circ \ldots \circ \zeta_{\omega_{j-1}}(a\mathfrak c^v_j)$, (7.7) $\mathfrak F_{j,n} := \{\tilde g^v_j \mid v \in \mathsf V^j_{2k_n} \text{ and } |1^\infty \wedge v| \geqslant n - j + D\}$, where $u \wedge v$ denotes the longest common prefix of two rays $u$ and $v$.” and “• Otherwise, that is, for indices $j \in \{1, \ldots, n\}$ other than those with $\omega_{j-1} = \mathbf 2$ and $n - k_n < j \leqslant n$, keep the single element $g_j$ and set $\mathfrak F_{j,n} = \{g_j\}$, where $g_j$ is defined in (7.1).” The condition $n - k_n < j$ is written $n < j + k_n$, which avoids truncated subtraction, and $|1^\infty \wedge v|$ is `commonPrefixLength v oneRay`. $\mathfrak F_{j,n}$ is a set of group elements, as in the paper; that distinct indices $v$ give distinct elements, behind the cardinality the paper states (“The cardinality of $\mathfrak F_{j,n}$ is $2^{\frac{2k_n - (n-j+\bar j)}{D}}$ in this case.”), is the milestone `ErschlerZheng.injOn_gTilde_and_ncard_fSet_eq`.
--   - `fProd`, `LambdaN`, `theta` and `upsilon` are (7.8)–(7.10), p. 40: “Take the direct product (7.8) $\mathfrak F_n = \prod_{i=1}^n \mathfrak F_{i,n}$ and the product of the hypercube $\{0, 1\}^n$ with $\mathfrak F_n$, (7.9) $\Lambda_n = \{0, 1\}^n \times \mathfrak F_n$. Define $\theta_n : \Lambda_n \to G_\omega$ to be the map $\theta_n((\boldsymbol\epsilon, \boldsymbol\gamma)) = \gamma_n^{\epsilon_n} \ldots \gamma_1^{\epsilon_1}$, where $\boldsymbol\epsilon = (\epsilon_1, \ldots, \epsilon_n) \in \{0, 1\}^n$ and $\boldsymbol\gamma = (\gamma_1, \ldots, \gamma_n)$, $\gamma_i \in \mathfrak F_{i,n}$. Take the measure $\upsilon_n$ on $G_\omega$ to be the push-forward of the uniform measure $\mathbf u_{\Lambda_n}$ under $\theta_n$, that is (7.10) $\upsilon_n(g) = \frac{|\{(\boldsymbol\epsilon, \boldsymbol\gamma) \in \Lambda_n : \theta_n((\boldsymbol\epsilon, \boldsymbol\gamma)) = g\}|}{|\Lambda_n|}$.” Coordinates are indexed from $0$: coordinate $i$ of `fProd` lies in $\mathfrak F_{i+1,n}$, and digit $i$ of $\boldsymbol\epsilon$ is $\epsilon_{i+1}$, a `Bool` used as the exponent $0$ or $1$. `upsilon` is a function on all of `BinaryTreeAut`; only its values at elements of $G_\omega$ enter $\mu_\beta$.
--   - `upsilonCheck` is p. 40: “For the purpose of symmetrization, set the measure $\check\upsilon_n$ to be $\check\upsilon_n(g) = \upsilon_n(g^{-1})$.”
--   - `normConst D β` and `muBeta D ω k β` are $C_\beta$ and $\mu_\beta$ of (7.11), p. 41: “Finally, for $\beta \in (0, 1)$, take the convex combination of the measures (7.11) $\mu_\beta = \frac12\mathbf u_S + \frac12\sum_{n \in \mathbb N, D|n} C_\beta 2^{-n\beta}(\upsilon_n + \check\upsilon_n)$, where $\mathbf u_S$ is the uniform measure on the generating set $\{a, b_\omega, c_\omega, d_\omega\}$, $C_\beta > 0$ is the normalization constant such that $\mu_\beta$ is a probability measure. Note that although suppressed in the notations, the measure $\mu_\beta$ depends on the sequence $(k_n)$.” The sum runs over $n \ge 1$ divisible by $D$: the paper's $k_n = A\lfloor\log_2 n\rfloor$ is not defined at $n = 0$. `normConst D β` is $(2\sum_{n \ge 1,\ D|n} 2^{-n\beta})^{-1}$; that $\mu_\beta$ is then a probability, for $\beta > 0$, is part of the milestone `ErschlerZheng.isProbability_and_hasFiniteEntropy_muBeta_and_mass_ball_compl_le`. The dependence on $(k_n)$ is the explicit argument `k`, and $\mu_\beta$ is a function on the elements of $G_\omega$ (`grigorchuk ω`). $\mathbf u_S$ is `uniformMeasure (genSet ω)`, uniform on the distinct elements among $a, b_\omega, c_\omega, d_\omega$; these are four distinct elements exactly when $\omega$ is not constant (`ErschlerZheng.ncard_gens_eq_four_iff_and_card_genSet_eq_four_iff`). The definitions accept every real $\beta$ and every $D$; every statement that uses them assumes the paper's ranges.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), pp. 35–42, §7.2 (g_n, W^n_k, V^j_k, h^v_i, 𝔠^v_j, g̃^v_j, 𝔉_{j,n}, Λ_n, θ_n, υ_n, μ_β)

import Definitions.Def_ErschlerZheng_Grigorchuk

/-!
# The construction of the measures `μ_β` (Erschler–Zheng §7.2, pp. 35–41)

A. Erschler and T. Zheng, *Growth of periodic Grigorchuk groups*, arXiv:1802.09077v2 (page
numbers of arXiv v2): the sequence `g_n` (7.1), the index sets `W^n_k` (7.2) and `V^j_k` (7.3),
the elements `h^v_i` (7.4), `𝔠^v_j` (7.5) and `g̃^v_j` (7.6), the sets `𝔉_{j,n}` (7.7), `𝔉_n` (7.8)
and `Λ_n` (7.9), the map `θ_n`, the measures `υ_n` (7.10) and `υ̌_n`, the standing assumption on
`(k_n)` (p. 40), the choice `k_n = A⌊log₂ n⌋` (p. 42), and the measure `μ_β` (7.11).

Conventions. Tree automorphisms are `Garrido.BinaryTreeAut`, acting on the right (`v <• g`).
Digits: `false` = 0, `true` = 1. Strings `ω : ℕ → Fin 3` are indexed from 0; the digits
`v_1 v_2 …` of a vertex are Lean's `v[0], v[1], …`. `⁅x, y⁆` is Mathlib's commutator
`x * y * x⁻¹ * y⁻¹` (`open scoped commutatorElement`). Elements and sets below live in
`BinaryTreeAut`; the measure `μ_β` is evaluated on the elements of `G_ω`.
-/

namespace ErschlerZheng
open scoped RightActions commutatorElement
open Garrido

/-- (7.1), p. 35: `g_n = ζ_{ω_0} ∘ ⋯ ∘ ζ_{ω_{n-1}}(ab_{𝔰ⁿω})` if `ω_{n-1} ≠ 2`, and
`ζ_{ω_0} ∘ ⋯ ∘ ζ_{ω_{n-1}}(ac_{𝔰ⁿω})` if `ω_{n-1} = 2`: the substitutions applied to the word
`ab` (or `ac`) over `{ab, ac, ad}`, and the resulting word evaluated in `G_ω`. -/
def seqG (ω : ℕ → Fin 3) (n : ℕ) : BinaryTreeAut :=
  evalWord ω 0 (((List.range n).foldr (fun i w => zetaWord (ω i) w)
    [if ω (n - 1) = 2 then APair.ac else APair.ab]).flatMap APair.toWord)

/-- (7.2), p. 37: `W^n_k = {u ∈ L_k : u = u_1 … u_k, u_i = 1 if n + i ∉ I_ω}` (the paper's `u_i`
is Lean's `u[i - 1]`). -/
def wSet (D : ℕ) (ω : ℕ → Fin 3) (n k : ℕ) : Set (List Bool) :=
  {u | u.length = k ∧ ∀ i (hi : i < u.length), n + (i + 1) ∉ frI D ω → u[i] = true}

/-- p. 37: `ℓ(k, j) = (1/D)(j + D - j̄ + k)`, where `j̄ = j % D` is the residue of `j` mod `D`. -/
def ellIndex (D k j : ℕ) : ℕ := (j + D - j % D + k) / D

/-- (7.3), p. 37: `V^j_k = {1^{D-j̄} u 1^{m_ℓ+2} 0 : u ∈ W^{j+D-j̄}_k}`, with `j̄ = j % D` and
`ℓ = ℓ(k, j)`. -/
def vSet (D : ℕ) (ω : ℕ → Fin 3) (j k : ℕ) : Set (List Bool) :=
  {v | ∃ u ∈ wSet D ω (j + D - j % D) k,
    v = List.replicate (D - j % D) true ++ u ++
      List.replicate (frM D ω (ellIndex D k j) + 2) true ++ [false]}

/-- (7.4), p. 38: `h^v_i = id` if `v_i = 1`, and `h^v_i = ι([b_{𝔰^{j+i-2}ω}, a], v_1 … v_{i-2})` if
`v_i = 0` (the paper's index `i ⩾ 1`; `v_i` is Lean's `v[i - 1]`, read as `1` beyond the end of
`v`). -/
def hElt (ω : ℕ → Fin 3) (j : ℕ) (v : List Bool) (i : ℕ) : BinaryTreeAut :=
  if v.getD (i - 1) true then 1
  else iota ⁅gen (shiftSeq ω (j + i - 2)) .b, grigA⁆ (v.take (i - 2))

/-- p. 38: the product `h^v_1 h^v_2 ⋯ h^v_{k'}`, where `k'` is the length of `v`. -/
def hProd (ω : ℕ → Fin 3) (j : ℕ) (v : List Bool) : BinaryTreeAut :=
  ((List.range v.length).map fun i => hElt ω j v (i + 1)).prod

/-- (7.5), p. 38: `𝔠^v_j = (h^v_1 ⋯ h^v_{k'})⁻¹ c_{𝔰^j ω} (h^v_1 ⋯ h^v_{k'})`. -/
def cElt (ω : ℕ → Fin 3) (j : ℕ) (v : List Bool) : BinaryTreeAut :=
  (hProd ω j v)⁻¹ * gen (shiftSeq ω j) .c * hProd ω j v

/-- (7.6), p. 39: `g̃^v_j = ζ_{ω_0} ∘ ⋯ ∘ ζ_{ω_{j-1}}(a𝔠^v_j)`, with each `ζ_{ω_i}` applied to group
elements as `zetaHat ω i`. -/
noncomputable def gTilde (ω : ℕ → Fin 3) (j : ℕ) (v : List Bool) : BinaryTreeAut :=
  (List.range j).foldr (fun i g => zetaHat ω i g) (grigA * cElt ω j v)

/-- p. 40: the standing assumption on `(k_n)`: a non-decreasing sequence whose terms `k_n`, for
`n ⩾ 1` divisible by `D`, are positive and divisible by `D`. -/
def IsAdmissibleSeq (D : ℕ) (k : ℕ → ℕ) : Prop :=
  Monotone k ∧ ∀ n, 1 ≤ n → D ∣ n → 0 < k n ∧ D ∣ k n

/-- p. 42: `k_n = A⌊log₂ n⌋`. -/
def kLog (A n : ℕ) : ℕ := A * Nat.log 2 n

/-- (7.7), p. 40: `𝔉_{j,n} = {g̃^v_j : v ∈ V^j_{2k_n}, |1^∞ ∧ v| ⩾ n - j + D}` if `ω_{j-1} = 2` and
`n - k_n < j ⩽ n`, and `𝔉_{j,n} = {g_j}` otherwise. -/
def fSet (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (j n : ℕ) : Set BinaryTreeAut :=
  if ω (j - 1) = 2 ∧ n < j + k n ∧ j ≤ n then
    {g | ∃ v ∈ vSet D ω j (2 * k n), n - j + D ≤ commonPrefixLength v oneRay ∧ g = gTilde ω j v}
  else {seqG ω j}

/-- (7.8), p. 40: `𝔉_n = ∏_{i=1}^n 𝔉_{i,n}` (Lean's coordinate `i` is the paper's `i + 1`). -/
abbrev fProd (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) : Type :=
  (i : Fin n) → ↥(fSet D ω k (i + 1) n)

/-- (7.9), p. 40: `Λ_n = {0, 1}ⁿ × 𝔉_n`. -/
abbrev LambdaN (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) : Type :=
  (Fin n → Bool) × fProd D ω k n

/-- p. 40: `θ_n((ε, γ)) = γ_n^{ε_n} ⋯ γ_1^{ε_1}`. -/
def theta (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) (p : LambdaN D ω k n) : BinaryTreeAut :=
  (List.ofFn fun i : Fin n => (p.2 i.rev : BinaryTreeAut) ^ (p.1 i.rev).toNat).prod

/-- (7.10), p. 40: `υ_n(g) = |{(ε, γ) ∈ Λ_n : θ_n((ε, γ)) = g}| / |Λ_n|`. -/
noncomputable def upsilon (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) : BinaryTreeAut → ℝ :=
  fun g => (Nat.card {p : LambdaN D ω k n // theta D ω k n p = g} : ℝ) / Nat.card (LambdaN D ω k n)

/-- p. 40: `υ̌_n(g) = υ_n(g⁻¹)`. -/
noncomputable def upsilonCheck (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) :
    BinaryTreeAut → ℝ :=
  fun g => upsilon D ω k n g⁻¹

/-- (7.11), p. 41: the constant `C_β = (2 ∑_{n ⩾ 1, D ∣ n} 2^{-nβ})⁻¹`. -/
noncomputable def normConst (D : ℕ) (β : ℝ) : ℝ :=
  (2 * ∑' n : ℕ, if 1 ≤ n ∧ D ∣ n then (2 : ℝ) ^ (-((n : ℝ) * β)) else 0)⁻¹

/-- (7.11), p. 41: `μ_β = ½ u_S + ½ ∑_{n ∈ ℕ, D ∣ n} C_β 2^{-nβ} (υ_n + υ̌_n)`, evaluated at the
elements of `G_ω`; `u_S` is the uniform measure on `S = {a, b_ω, c_ω, d_ω}`. -/
noncomputable def muBeta (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (β : ℝ) : grigorchuk ω → ℝ :=
  fun g => (1 / 2) * uniformMeasure (genSet ω) g +
    (1 / 2) * ∑' n : ℕ, if 1 ≤ n ∧ D ∣ n then
      normConst D β * (2 : ℝ) ^ (-((n : ℝ) * β)) *
        (upsilon D ω k n g + upsilonCheck D ω k n g) else 0

end ErschlerZheng


