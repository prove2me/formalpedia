-- Prove2me | Definitions.Def_AlgCoverage_OddOrder_Coverage
-- name    : AlgCoverage_OddOrder_Coverage
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:45:30.252365+00:00
-- url     : https://prove2.me/theorems/84d26c99-230e-423d-b2f7-f21bc7100cc8
-- title:
--   Ordered subset products of k group inputs, the iid and ordered-distinct sampling laws, coverage probabilities, medians, hole counts and the seed scale $c_N$, $k_0$, $\lambda_0$
-- statement:
--   Let $G$ be a finite group of order $N$ and $x=(X_1,\dots,X_k)\in G^k$ an input list. For a **selector** (mask) $v\in\{0,1\}^k$ the **ordered subset product** is
--   $$W_v=X_1^{v_1}X_2^{v_2}\cdots X_k^{v_k},$$
--   multiplied in input order (the group need not be commutative); the empty selector gives $W_0=1_G$. The **word set** is $\mathcal W_k=\{W_v : v\in\{0,1\}^k\}$, and the list **covers** $G$ when $\mathcal W_k=G$. A target set $B\subseteq G$ is **avoided** when $B\cap\mathcal W_k=\varnothing$.
--
--   Two sampling laws are used. In the **iid model** $X_1,\dots,X_k$ are independent uniform elements of $G$: an event $A$ has probability $\Pr_{\rm iid}(A)=\#\{x\in G^k : A(x)\}/N^k$, and expectations are $\mathbb E f=N^{-k}\sum_{x\in G^k} f(x)$. In the **ordered-distinct model** the inputs are a uniform ordered $k$-tuple of distinct elements, legal for $k\le N$: $\Pr_{\rm od}(A)=\#\{x \text{ injective} : A(x)\}/\#\{x\text{ injective}\}$, which is the iid law conditioned on distinct inputs.
--
--   The **coverage medians** are the least legal lengths with coverage probability at least one half:
--   $$f_{\rm iid}(G)=\min\{k\ge0 : \Pr_{\rm iid}(\mathcal W_k=G)\ge 1/2\},\qquad f_{\rm od}(G)=\min\{k\le N : \Pr_{\rm od}(\mathcal W_k=G)\ge 1/2\}.$$
--   The **hole count** $H=\#\{g\ne1_G : g\notin\mathcal W_k\}$ counts missed nonidentity elements, and the **missing fraction** is $F=|G\setminus\mathcal W_k|/N$.
--
--   The seed scale is $c_N=\log_2(N\ln N)$, the seed length $k_0=\lfloor c_N-80\rfloor$, and $\lambda_0=(2^{k_0}-1)/N$; for a target count $m$, the adjusted seed of Corollary 3.3 is $k_B=\lfloor \log_2(N\ln N/m)-80\rfloor$.
--
--   **Formalization Note.** Selectors are `Fin k → Bool` (0-based positions); `word x v` is `List.prod` of `List.ofFn` in increasing position. Probabilities are exact counting ratios in `ℝ` (`probIid`, `probOd`, `expIid`). For an illegal length $k>N$ there are no injective tuples and `probOd` is the junk value $0$; statements use it only for $k\le N$ or for lengths that are legal for all large $N$. The medians use `sInf` on `ℕ`; both defining sets are nonempty for every finite group (the od set contains $k=N$, where coverage is sure; the iid coverage probability tends to one as $k\to\infty$), so `sInf` is a true minimum. `cN`, `lam0` are reals, `k0` and `kB` are integers (`Int.floor`), and $\lambda_0$ uses the integer power $2^{k_0}$.
-- source:
--   Lin, Sharp Second-Order Thresholds for Random Algebraic Coverage, STOC 2027 submission (manuscript sha256 9db96430…), p. 1 (PDF 2), §1; pp. 5–7 (PDF 6–8), §2.1 and §3.1; p. 8 (PDF 9), Corollaries 3.2, 3.3 and Theorem 3.4; p. 27 (PDF 28), §9.1

import Mathlib

namespace AlgCoverage.OddOrder

/-- The ordered subset product `W_v = X₁^{v₁} ⋯ X_k^{v_k}` of the inputs `x = (X₁, …, X_k)` selected by
the mask `v ∈ {0,1}^k` (encoded as `Fin k → Bool`), multiplied **in input order** (noncommutative).
The empty mask gives the empty product `1_G`. Lin, §1 and §3.1, printed pp. 1 and 7 (PDF 2 and 8). -/
def word {G : Type*} [Group G] {k : ℕ} (x : Fin k → G) (v : Fin k → Bool) : G :=
  (List.ofFn fun i : Fin k => if v i then x i else 1).prod

/-- The word set `𝒲_k = {W_v : v ∈ {0,1}^k}` (the empty product `1_G` included). -/
def wordSet {G : Type*} [Group G] {k : ℕ} (x : Fin k → G) : Set G :=
  Set.range (word x)

/-- Coverage: `𝒲_k = G`. -/
def Covers {G : Type*} [Group G] {k : ℕ} (x : Fin k → G) : Prop :=
  wordSet x = Set.univ

/-- Avoidance of a target set: `B ∩ 𝒲_k = ∅`. -/
def Avoids {G : Type*} [Group G] {k : ℕ} (B : Finset G) (x : Fin k → G) : Prop :=
  ∀ g ∈ B, g ∉ wordSet x

/-- **iid model.** The probability of an event `A` of the input tuple when `X₁, …, X_k` are independent
uniform elements of the finite group `G`: the counting ratio `#{x ∈ G^k : A x} / N^k`, `N = |G|`. -/
noncomputable def probIid (G : Type*) [Fintype G] (k : ℕ) (A : (Fin k → G) → Prop) : ℝ :=
  (Nat.card {x : Fin k → G // A x} : ℝ) / (Fintype.card G : ℝ) ^ k

/-- Expectation of a real function of the input tuple in the iid model: `N^{-k} ∑_{x ∈ G^k} f(x)`. -/
noncomputable def expIid (G : Type*) [Fintype G] (k : ℕ) (f : (Fin k → G) → ℝ) : ℝ :=
  (∑ x : Fin k → G, f x) / (Fintype.card G : ℝ) ^ k

/-- **Ordered-distinct model.** The probability of an event `A` when the inputs are a uniform ordered
`k`-tuple of distinct elements of `G` (uniform on injective tuples):
`#{x injective : A x} / #{x injective}`. It is the iid law conditioned on distinct inputs. The model
is only used for legal lengths `k ≤ |G|`; for `k > |G|` there are no injective tuples and the ratio
is the junk value `0`. -/
noncomputable def probOd (G : Type*) [Fintype G] (k : ℕ) (A : (Fin k → G) → Prop) : ℝ :=
  (Nat.card {x : Fin k → G // Function.Injective x ∧ A x} : ℝ) /
    (Nat.card {x : Fin k → G // Function.Injective x} : ℝ)

/-- iid coverage probability `Pr_iid(𝒲_k = G)`. -/
noncomputable def covIid (G : Type*) [Group G] [Fintype G] (k : ℕ) : ℝ :=
  probIid G k Covers

/-- Ordered-distinct coverage probability `Pr_od(𝒲_k = G)` (legal for `k ≤ |G|`). -/
noncomputable def covOd (G : Type*) [Group G] [Fintype G] (k : ℕ) : ℝ :=
  probOd G k Covers

/-- The iid coverage median `f_iid(G) = min{k : Pr_iid(𝒲_k = G) ≥ 1/2}` (every `k ≥ 0` is legal).
Encoded with `sInf` on `ℕ`; the set is nonempty for every finite group (coverage probability tends
to one as `k → ∞`), so the junk value of `sInf ∅` never occurs. -/
noncomputable def fIid (G : Type*) [Group G] [Fintype G] : ℕ :=
  sInf {k : ℕ | (1 : ℝ) / 2 ≤ covIid G k}

/-- The ordered-distinct coverage median `f_od(G) = min{k ≤ |G| : Pr_od(𝒲_k = G) ≥ 1/2}` (legal
lengths only). The set contains `k = |G|`, where coverage is sure, so `sInf` is a true minimum. -/
noncomputable def fOd (G : Type*) [Group G] [Fintype G] : ℕ :=
  sInf {k : ℕ | k ≤ Fintype.card G ∧ (1 : ℝ) / 2 ≤ covOd G k}

/-- The hole count: the number of missed nonidentity elements, `#{g ≠ 1_G : g ∉ 𝒲_k}`. -/
noncomputable def holes {G : Type*} [Group G] {k : ℕ} (x : Fin k → G) : ℕ :=
  Nat.card {g : G // g ≠ 1 ∧ g ∉ wordSet x}

/-- The missing fraction `F = |G \ 𝒲_k| / |G|`. -/
noncomputable def missingFrac {G : Type*} [Group G] [Fintype G] {k : ℕ} (x : Fin k → G) : ℝ :=
  (Nat.card {g : G // g ∉ wordSet x} : ℝ) / (Fintype.card G : ℝ)

/-- The seed scale `c_N = log₂(N ln N)` (a real number; meaningful for `N ≥ 2`). -/
noncomputable def cN (N : ℕ) : ℝ :=
  Real.logb 2 ((N : ℝ) * Real.log N)

/-- The seed length `k₀ = ⌊c_N − 80⌋ ∈ ℤ` (positive for all large `N`; as a sample length it is used
through `Int.toNat`). -/
noncomputable def k0 (N : ℕ) : ℤ :=
  ⌊cN N - 80⌋

/-- `λ₀ = (2^{k₀} − 1)/N` (with the integer power `2^{k₀}`). -/
noncomputable def lam0 (N : ℕ) : ℝ :=
  ((2 : ℝ) ^ (k0 N) - 1) / (N : ℝ)

/-- The adjusted seed of Corollary 3.3 for `m` targets: `k_B = ⌊log₂(N ln N / m) − 80⌋ ∈ ℤ`. -/
noncomputable def kB (N m : ℕ) : ℤ :=
  ⌊Real.logb 2 ((N : ℝ) * Real.log N / (m : ℝ)) - 80⌋

end AlgCoverage.OddOrder


