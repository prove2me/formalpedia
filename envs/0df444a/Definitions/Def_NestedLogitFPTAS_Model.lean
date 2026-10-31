-- Prove2me | Definitions.Def_NestedLogitFPTAS_Model
-- name    : NestedLogitFPTAS_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:25:50.680882+00:00
-- url     : https://prove2.me/theorems/6643755e-7a78-498a-9687-7f08f52f5755
-- title:
--   §1.1, pp.2–3 — the capacitated Nested Logit model and the quantities $\omega$, $\rho$, $W^\uparrow$, $W^\downarrow$, $\pi_{\min}$
-- statement:
--   An instance has $n$ products partitioned into $M$ nests $N_1,\dots,N_M$. Product $i$ has a selling price $r_i$, a preference weight $w_i$ and a cost $c_i$. Nest $m$ has a no-purchase weight $w_{0m}$ and a dissimilarity parameter $\gamma_m$; $w_0$ is the outside no-purchase weight, and $\mathcal C$ is the bound on the total cost.
--
--   For $T\subseteq N_m$ let $w_+(T)=\mathbb I[T\neq\emptyset]\,(w_{0m}+w(T))$ and $\mathcal R_m(T)=\sum_{i\in T}r_i\,w_i/w_+(T)$. An assortment $S=(S_1,\dots,S_M)$ earns
--   $$
--   \mathcal R(S)=\sum_{m=1}^M\mathcal R_m(S_m)\,\nu(m,S),\qquad \nu(m,S)=\frac{w_+(S_m)^{\gamma_m}}{w_0+\sum_{\mu=1}^M w_+(S_\mu)^{\gamma_\mu}},
--   $$
--   and it is $\mathcal C$-feasible when $\sum_m c(S_m)\le\mathcal C$.
--
--   The module also defines the sums $\omega_{[j,k]}(S)=\sum_{m=j}^k w_+(S_m)^{\gamma_m}$ and $\rho_{[j,k]}(S)=\sum_{m=j}^k\mathcal R_m(S_m)\,w_+(S_m)^{\gamma_m}$ of §2.1, as well as $\gamma^+=\max\{1,\gamma_1,\dots,\gamma_M\}$, $\gamma^-=\min\{1,\gamma_1,\dots,\gamma_M\}$, and $W^\uparrow$, $W^\downarrow$, $r_{\max}$, $r_{\min}$, $\pi_{\min}$ of §3.3. Every other object of the mission builds on these.
--
--   **Formalization Note** Products are `Fin n`, the partition is a map `nest : Fin n → Fin M`, and an assortment is one `Finset (Fin n)` with $S_m$ = `part S m`. `Standing` collects $r_i,w_i>0$ and the paper's presuppositions: $M\ge1$, nonempty nests, $\gamma_m>0$ (at $\gamma_m=0$ the ratio $\gamma^+/\gamma^-$ is undefined), and nonnegative $w_0,w_{0m}$. No sign is imposed on $c$ or $\mathcal C$. At $w_0=0$ and $S=\emptyset$, Lean's $x/0=0$ gives $\mathcal R(\emptyset)=0$. `omegaRange j k` uses the paper's indices $1\le j,k\le M$.
-- source:
--   Segev, Approximation Schemes for Capacity-Constrained Assortment Optimization under the Nested Logit Model, SSRN #3553264 (Mar 2020), §1.1, pp.2–3; §2.1, p.7; §3.3, pp.11–12; Theorem 1.1, p.6

import Mathlib

namespace NestedLogitFPTAS

/-- **The capacitated Nested Logit instance.** Segev, *Approximation Schemes for
Capacity-Constrained Assortment Optimization under the Nested Logit Model*, SSRN #3553264
(Mar 2020), §1.1, pp.2–3.

There are `n` products and `M` nests; `nest i` is the nest of product `i`, `r`, `w`, `c` are
selling prices, preference weights and costs, `w0` is the outside no-purchase weight, `w0n m` the
no-purchase weight of nest `m`, `γ m` the dissimilarity parameter of nest `m`, and `C` the bound on
the total cost.

**Formalization Note.** Products are `Fin n`, and a map `nest` gives the partition `N₁, …, N_M` at
once. An assortment `S = (S₁, …, S_M)` is a single `S : Finset (Fin n)` with `Sₘ = part S m`. -/
structure Instance (n M : ℕ) where
  nest : Fin n → Fin M
  r : Fin n → ℝ
  w : Fin n → ℝ
  c : Fin n → ℝ
  w0 : ℝ
  w0n : Fin M → ℝ
  γ : Fin M → ℝ
  C : ℝ

/-- Maximum of `f` over a finite set; `0` on the empty set, which `Standing` excludes wherever the
paper takes a maximum. -/
noncomputable def maxOn {ι : Type*} (s : Finset ι) (f : ι → ℝ) : ℝ :=
  if h : s.Nonempty then s.sup' h f else 0

/-- Minimum of `f` over a finite set; `0` on the empty set, which `Standing` excludes wherever the
paper takes a minimum. -/
noncomputable def minOn {ι : Type*} (s : Finset ι) (f : ι → ℝ) : ℝ :=
  if h : s.Nonempty then s.inf' h f else 0

namespace Instance

variable {n M : ℕ} (I : Instance n M)

/-- The standing assumptions of §1.1, pp.2–3: `rᵢ > 0`, `wᵢ > 0`.

**Formalization Note.** `0 < M`, nonempty nests (`Surjective nest`) and `γ m > 0` are the paper's
presuppositions: `W↓`, `r_min` and `π_min` minimize over `Nₘ`, and at `γₘ = 0` the ratio `γ⁺/γ⁻` and
the power `ωₖ^{1/γₖ}` are undefined although §1.1 says "non-negative". `0 ≤ w0` and `0 ≤ w0n m` are
the signs of weights. No sign is imposed on `c` or `C`. -/
structure Standing : Prop where
  pos_M : 0 < M
  surj : Function.Surjective I.nest
  r_pos : ∀ i, 0 < I.r i
  w_pos : ∀ i, 0 < I.w i
  w0_nonneg : 0 ≤ I.w0
  w0n_nonneg : ∀ m, 0 ≤ I.w0n m
  γ_pos : ∀ m, 0 < I.γ m

/-- `Nₘ`, the set of products of nest `m`, §1.1, p.2. -/
def nestSet (m : Fin M) : Finset (Fin n) := Finset.univ.filter (fun i => I.nest i = m)

/-- `Sₘ`, the part of the assortment `S` in nest `m`, §1.1, p.2. -/
def part (S : Finset (Fin n)) (m : Fin M) : Finset (Fin n) := S.filter (fun i => I.nest i = m)

/-- `w₊(T) = 𝕀[T ≠ ∅]·(w₀ₘ + w(T))`, §1.1, p.3, for `T ⊆ Nₘ`. -/
noncomputable def wplus (m : Fin M) (T : Finset (Fin n)) : ℝ :=
  if T.Nonempty then I.w0n m + ∑ i ∈ T, I.w i else 0

/-- `Rₘ(T) = Σ_{i∈T} rᵢ·π(i,T)` with `π(i,T) = wᵢ/w₊(T)`, §1.1, p.3. -/
noncomputable def Rnest (m : Fin M) (T : Finset (Fin n)) : ℝ :=
  ∑ i ∈ T, I.r i * (I.w i / I.wplus m T)

/-- `ν(m,S) = w₊(Sₘ)^{γₘ} / (w₀ + Σ_µ w₊(S_µ)^{γ_µ})`, §1.1, pp.2–3. -/
noncomputable def nu (m : Fin M) (S : Finset (Fin n)) : ℝ :=
  I.wplus m (I.part S m) ^ I.γ m / (I.w0 + ∑ μ, I.wplus μ (I.part S μ) ^ I.γ μ)

/-- The expected revenue `R(S) = Σₘ Rₘ(Sₘ)·ν(m,S)`, §1.1, p.3.

**Formalization Note.** At `w₀ = 0` and `S = ∅` the paper's formula is `0/0`; Lean's `x / 0 = 0`
gives `R(∅) = 0`, the revenue of offering nothing. -/
noncomputable def R (S : Finset (Fin n)) : ℝ :=
  ∑ m, I.Rnest m (I.part S m) * I.nu m S

/-- The total cost `c(T)`. -/
def cost (T : Finset (Fin n)) : ℝ := ∑ i ∈ T, I.c i

/-- `S` is `C`-feasible: `Σₘ c(Sₘ) ≤ C`, §1.1, p.2. The parts partition `S`, so this is
`c(S) ≤ C`. -/
def Feasible (S : Finset (Fin n)) : Prop := I.cost S ≤ I.C

/-- `ω[j,k](S) = Σ_{m=j}^k w₊(Sₘ)^{γₘ}`, §2.1, p.7, with the paper's indices `1 ≤ j, k ≤ M` (nest
`m : Fin M` is the paper's nest `m + 1`); an empty range gives `0`. -/
noncomputable def omegaRange (j k : ℕ) (S : Finset (Fin n)) : ℝ :=
  ∑ m ∈ Finset.univ.filter (fun m : Fin M => j ≤ m.val + 1 ∧ m.val + 1 ≤ k),
    I.wplus m (I.part S m) ^ I.γ m

/-- `ρ[j,k](S) = Σ_{m=j}^k Rₘ(Sₘ)·w₊(Sₘ)^{γₘ}`, §2.1, p.7, with the paper's indices. -/
noncomputable def rhoRange (j k : ℕ) (S : Finset (Fin n)) : ℝ :=
  ∑ m ∈ Finset.univ.filter (fun m : Fin M => j ≤ m.val + 1 ∧ m.val + 1 ≤ k),
    I.Rnest m (I.part S m) * I.wplus m (I.part S m) ^ I.γ m

/-- `γ⁺ = max{1, γ₁, …, γ_M}`, Theorem 1.1, p.6. -/
noncomputable def gammaPlus : ℝ := max (maxOn Finset.univ I.γ) 1

/-- `γ⁻ = min{1, γ₁, …, γ_M}`, Theorem 1.1, p.6. -/
noncomputable def gammaMinus : ℝ := min (minOn Finset.univ I.γ) 1

/-- `W↑ = max{max_m{w₀ₘ + w(Nₘ)}, 1}`, §3.3, p.11. -/
noncomputable def wUp : ℝ :=
  max (maxOn Finset.univ (fun m => I.w0n m + ∑ i ∈ I.nestSet m, I.w i)) 1

/-- `W↓ = min{min_m{w₀ₘ + min_{i∈Nₘ} wᵢ}, 1}`, §3.3, p.11. -/
noncomputable def wDown : ℝ :=
  min (minOn Finset.univ (fun m => I.w0n m + minOn (I.nestSet m) I.w)) 1

/-- `r_max`, the largest selling price, §3.3, p.12. -/
noncomputable def rMax : ℝ := maxOn Finset.univ I.r

/-- `r_min`, the smallest selling price, §3.3, p.12. -/
noncomputable def rMin : ℝ := minOn Finset.univ I.r

/-- `π_min = min_m (min_{i∈Nₘ} wᵢ) / w₊(Nₘ)`, §3.3, p.12. -/
noncomputable def piMin : ℝ :=
  minOn Finset.univ (fun m => minOn (I.nestSet m) I.w / I.wplus m (I.nestSet m))

end Instance

end NestedLogitFPTAS


