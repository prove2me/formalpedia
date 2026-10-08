-- Prove2me | Definitions.Def_AffinePolicies_TwoGap_Setting
-- name    : AffinePolicies_TwoGap_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T06:15:15.939163+00:00
-- url     : https://prove2.me/theorems/ed9f5455-a664-4183-93bf-b10086303fe0
-- title:
--   (1), (6), Def. 2, (10), PDF pp. 2, 8, 11 — Π_Adapt(𝒰), z_Adapt, z_Aff, the instance ℐ of (6), permutation invariance and Γ
-- statement:
--   This file fixes the special instance of Section 3 of Bertsimas and Goyal. The two-stage adaptive linear problem (1) it instantiates is defined in the shared setting file `AffinePolicies.Simplex.Setting`, recalled below.
--
--   **The model (1).** Given $A \in \mathbb R^{m\times n_1}$, $B \in \mathbb R^{m\times n_2}$, $c \in \mathbb R^{n_1}$, $d \in \mathbb R^{n_2}$ and an uncertainty set $\mathcal U \subseteq \mathbb R^m$, the problem $\Pi_{\mathrm{Adapt}}(\mathcal U)$ is
--   $$z_{\mathrm{Adapt}}(\mathcal U)=\min\ c^{T}x+\max_{b\in\mathcal U} d^{T}y(b)\quad\text{s.t.}\quad Ax+By(b)\ge b,\ \ x\ge 0,\ y(b)\ge 0\quad\forall b\in\mathcal U .$$
--
--   1. A pair $(x, y)$, with $x \in \mathbb R^{n_1}$ and $y : \mathbb R^m \to \mathbb R^{n_2}$, is **feasible** if $x \ge 0$ and, for every $b \in \mathcal U$, $y(b) \ge 0$ and $Ax + By(b) \ge b$ (componentwise).
--   2. A real number $t$ **bounds the worst-case cost** of $(x,y)$ if $c^{T}x + d^{T}y(b) \le t$ for all $b \in \mathcal U$.
--   3. $z_{\mathrm{Adapt}}(\mathcal U)$ is the infimum of all such bounds $t$ over feasible pairs.
--   4. An **affine policy** is $y(b) = Pb + q$ with $P \in \mathbb R^{n_2\times m}$ and $q \in \mathbb R^{n_2}$; $z_{\mathrm{Aff}}(\mathcal U)$ is the same infimum taken over the feasible pairs whose second-stage policy is affine (so the policy must be nonnegative on $\mathcal U$).
--   5. A feasible pair (respectively a feasible affine pair) is **optimal** if its worst-case cost is bounded by every bound achieved by any feasible pair (respectively any feasible affine pair).
--
--   **The instance $\mathcal I$ of (6).** Take $n_1 = n_2 = m$, $c = 0$, $d = (1,\dots,1)^{T}$, $A = 0$, $B_{ii} = 1$ and $B_{ij} = 1/\sqrt m$ for $i \ne j$, and
--   $$\mathcal U=\operatorname{conv}\{b^0,b^1,\dots,b^{m+2}\},$$
--   where $b^0 = 0$, $b^j = e_j$ (the $j$-th unit vector) for $j = 1,\dots,m$, $b^{m+1}$ has $1/\sqrt m$ in its first $m/2$ coordinates and $0$ elsewhere, and $b^{m+2}$ has $0$ in its first $m/2$ coordinates and $1/\sqrt m$ in its last $m/2$.
--
--   **Permutations.** For a permutation $\tau$ of $\{1,\dots,m\}$ and $x \in \mathbb R^m$, write $x^{\tau} = (x_{\tau(1)},\dots,x_{\tau(m)})$. A set $U \subseteq \mathbb R^m$ is **permutation-invariant** with respect to $\tau$ (Definition 2) if $x \in U \iff x^{\tau} \in U$. Finally, (10) defines
--   $$\Gamma=\{\tau\in S^m \mid i\le m/2 \iff \tau(i)\le m/2\},$$
--   the permutations that map the first half of the coordinates onto itself.
--
--   These objects are the setting of Theorem 2, which shows that on $\mathcal I$ the best affine policy costs more than $(2-\delta)$ times the fully adaptable optimum.
--
--   **Formalization Note** The model (1) — `Feasible`, `CostLE`, `zAdapt`, `affinePolicy`, `zAff`, `IsOptimalAdapt`, `IsOptimalAff` — is imported from `AffinePolicies.Simplex` (module `Definitions.Def_AffinePolicies_Simplex_Setting`); this file adds the instance, Definition 2 and $\Gamma$. Vectors are `Fin m → ℝ` with the componentwise order; $Bx$ and $d^{T}y$ are `B *ᵥ x` and `d ⬝ᵥ y`. The optimal values are infima of epigraph sets (the sets of achievable worst-case bounds), so they take Lean's junk value $0$ on an instance with no feasible solution; the instance $\mathcal I$ is feasible (Lemma 1, and the affine policy $y \equiv e$). Coordinates are 0-based: the paper's coordinate $i$ is index $i-1$, so "$i \le m/2$" reads `(i : ℕ) < m / 2` (natural-number division, exact for even $m$). $x^{\tau}$ is `x ∘ τ`. Definition 2 prints "$x \in P \iff x^{\tau} \in P$", a slip for the set $U$; the definition uses $U$.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, (1) PDF p. 2; (6) PDF p. 8; notation (i)–(ii), Definition 2 and (10), PDF pp. 10–11; affine policies as in Theorem 1, PDF p. 6

import Mathlib
import Definitions.Def_AffinePolicies_Simplex_Setting

namespace AffinePolicies.TwoGap

open Matrix

variable {m n₁ n₂ : ℕ}

/-! ### The instance ℐ of (6), with `n₁ = n₂ = m` -/

/-- `A_ij = 0`. -/
def A6 (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := 0

/-- `B_ij = 1` if `i = j`, `1/√m` otherwise. -/
noncomputable def B6 (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => if i = j then 1 else 1 / Real.sqrt m

/-- `c = 0`. -/
def c6 (m : ℕ) : Fin m → ℝ := 0

/-- `d = (1, …, 1)ᵀ`. -/
def d6 (m : ℕ) : Fin m → ℝ := fun _ => 1

/-- `b^{m+1}`: `1/√m` on the first `m/2` coordinates (0-based indices `0, …, m/2 - 1`),
`0` on the rest. -/
noncomputable def bLow (m : ℕ) : Fin m → ℝ :=
  fun i => if (i : ℕ) < m / 2 then 1 / Real.sqrt m else 0

/-- `b^{m+2}`: `0` on the first `m/2` coordinates, `1/√m` on the last `m/2`. -/
noncomputable def bHigh (m : ℕ) : Fin m → ℝ :=
  fun i => if m / 2 ≤ (i : ℕ) then 1 / Real.sqrt m else 0

/-- `𝒰 = conv{b⁰, b¹, …, b^{m+2}}` with `b⁰ = 0`, `bʲ = e_j` (`j = 1, …, m`),
`b^{m+1} = bLow m`, `b^{m+2} = bHigh m`. -/
noncomputable def U6 (m : ℕ) : Set (Fin m → ℝ) :=
  convexHull ℝ ({0} ∪ Set.range (fun j : Fin m => (Pi.single j (1 : ℝ) : Fin m → ℝ)) ∪
    {bLow m, bHigh m})

/-! ### Permutations: Definition 2 and the set Γ of (10) -/

/-- Definition 2: `U` is permutation-invariant with respect to `τ` iff
`x ∈ U ↔ x^τ ∈ U` for all `x`, where `x^τ = (x_{τ(1)}, …, x_{τ(m)}) = x ∘ τ`. -/
def IsPermInvariant (U : Set (Fin m → ℝ)) (τ : Equiv.Perm (Fin m)) : Prop :=
  ∀ x : Fin m → ℝ, x ∈ U ↔ x ∘ τ ∈ U

/-- (10): `Γ = {τ ∈ S^m | i ≤ m/2 ↔ τ(i) ≤ m/2}`; with 0-based indices the paper's
`i ≤ m/2` reads `(i : ℕ) < m / 2`. -/
def Gamma (m : ℕ) : Set (Equiv.Perm (Fin m)) :=
  {τ | ∀ i : Fin m, (i : ℕ) < m / 2 ↔ ((τ i : Fin m) : ℕ) < m / 2}

end AffinePolicies.TwoGap


