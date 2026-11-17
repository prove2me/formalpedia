-- Prove2me | Definitions.Def_DeepQOperator_Supplement_Envelope
-- name    : DeepQOperator_Supplement_Envelope
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:39:33.260135+00:00
-- url     : https://prove2.me/theorems/5ea0038a-5de3-4013-af19-23d6d94ab746
-- title:
--   The three-row envelope family (13)–(14) and its response mixing
-- statement:
--   Fix $m\ge2$. The parameter is $\theta=(s,z_1,\dots,z_m)\in[0,m+1]\times[0,1]^m$, with two known anchor payloads $z_0=z_{m+1}=0$. For $0\le j\le m+1$ let $b_j(s)=2js-j^2$, and define the three critic rows
--   $$
--   A(s,z)=\max_{0\le j\le m+1}\{z_j+b_j(s)\},\qquad B(s)=\max_{0\le j\le m+1}b_j(s),\qquad C(z)=\max_{1\le j\le m}z_j .
--   $$
--   Decision $+$ has response $w_+=(1,0,0)$ and reward $r_+=-\gamma/2$. Decision $-$ has $w_-=(0,1,0)$ and $r_-=0$. The Bellman scores are $t_a=r_a+\gamma\,w_a^{\mathsf T}(A,B,C)$, the contrast is $t_+-t_-=\gamma(A-B-1/2)$, and the decision loss is $\ell(a,\theta)=\max_b t_b(\theta)-t_a(\theta)$.
--
--   The **raw sites** are the affine expressions inside each maximum: $z_j+b_j(s)$ and $b_j(s)$ for $0\le j\le m+1$, and $z_j$ for $1\le j\le m$ (the $3m+4$ listed sites).
--
--   **Response mixing** with weight $0<\lambda<1$ replaces each response $w_a$ by $(1-\lambda)w_a+\lambda(1,1,1)/3$ and each reward $r_a$ by $(1-\lambda)r_a$. The mixed scores are computed from (1) with these weights; $\lambda=0$ is the unmixed family.
--
--   This family carries the paper's fixed-accuracy separation (Theorems 4, 5, 7, 11).
--
--   **Formalization Note** Coordinates are $\{s\}\sqcup\{1,\dots,m\}$. Anchor indices run over $\{0,\dots,m+1\}$, and $z_0=z_{m+1}=0$ is built in. Row C is a real supremum over $m\ge1$ indices, hence a maximum.
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), §4 eqs. (13)–(14), p.6 (PDF p.9); 'Strict positivity', p.7 (PDF p.10)

import Mathlib
import Definitions.Def_DeepQOperator_Family

open Finset

namespace DeepQOperator.Supplement

/-!
# The three-row envelope family (13)–(14) and its response mixing

Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), §4 eqs. (13)–(14) p.6 (PDF p.9),
"Strict positivity" p.7 (PDF p.10).

Fix `m ≥ 2`. The parameter is `θ = (s, z_1, …, z_m) ∈ [0, m+1] × [0,1]^m`, with the two known anchor
payloads `z_0 = z_{m+1} = 0`. For `0 ≤ j ≤ m+1` put `b_j(s) = 2js − j²`, and define the rows
`A(s,z) = max_{0≤j≤m+1} (z_j + b_j(s))`, `B(s) = max_{0≤j≤m+1} b_j(s)`, `C(z) = max_{1≤j≤m} z_j`.
The responses `w₊ = (1,0,0)`, `w₋ = (0,1,0)` and rewards `r₊ = −γ/2`, `r₋ = 0` give the contrast
`g_m = γ(A − B − 1/2)`. The expressions inside each maximum, including the individual `z_j` of row C,
are the raw oracle sites. Response mixing with `0 < λ < 1` replaces `w_a` by
`(1 − λ) w_a + λ(1,1,1)/3` and `r_a` by `(1 − λ) r_a`.

**Formalization Note.**
* The coordinates are `Unit ⊕ Fin m`: `Sum.inl ()` is the address `s`, `Sum.inr i` is the payload
  `z_{i+1}`. Anchor indices `j ∈ {0, …, m+1}` are `Fin (m+2)`; `envZ m θ j` is `z_j`, equal to `0` at
  `j = 0` and `j = m+1`.
* Row C is the real supremum over `Fin m`, which is the maximum for `m ≥ 1` (all theorems take
  `m ≥ 2`).
* The scores are the Bellman scores (1) built with `bellmanScore` from the mixed responses and
  rewards; `λ = 0` is the unmixed family. `envLoss m γ λ a θ` is the decision loss (3); `true` is the
  action `+`.
* The raw dictionary is the set of the listed affine sites: `z_j + b_j(s)` and `b_j(s)` for
  `0 ≤ j ≤ m+1` (at `j = 0` and `j = m+1` the first coincides with the second because the anchors are
  zero), and `z_j` for `1 ≤ j ≤ m`.
-/

/-- Coordinates of the envelope family: the address `s` and the payloads `z_1, …, z_m`. -/
abbrev EnvCoord (m : ℕ) : Type := Unit ⊕ Fin m

/-- The parameter box `[0, m+1] × [0,1]^m`. -/
def envBox (m : ℕ) : Set (EnvCoord m → ℝ) :=
  {θ | θ (Sum.inl ()) ∈ Set.Icc (0 : ℝ) (m + 1) ∧ ∀ i : Fin m, θ (Sum.inr i) ∈ Set.Icc (0 : ℝ) 1}

/-- The payload `z_j` for `0 ≤ j ≤ m+1`, with anchors `z_0 = z_{m+1} = 0`. -/
def envZ (m : ℕ) (θ : EnvCoord m → ℝ) (j : Fin (m + 2)) : ℝ :=
  if h : 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ m then θ (Sum.inr ⟨(j : ℕ) - 1, by omega⟩) else 0

/-- `b_j(s) = 2js − j²` of (13). -/
def envB (j : ℕ) (s : ℝ) : ℝ := 2 * (j : ℝ) * s - (j : ℝ) ^ 2

/-- Row A: `max_{0≤j≤m+1} (z_j + b_j(s))`. -/
noncomputable def envRowA (m : ℕ) (θ : EnvCoord m → ℝ) : ℝ :=
  Finset.univ.sup' ⟨0, Finset.mem_univ _⟩ (fun j : Fin (m + 2) => envZ m θ j + envB j (θ (Sum.inl ())))

/-- Row B: `max_{0≤j≤m+1} b_j(s)`. -/
noncomputable def envRowB (m : ℕ) (θ : EnvCoord m → ℝ) : ℝ :=
  Finset.univ.sup' ⟨0, Finset.mem_univ _⟩ (fun j : Fin (m + 2) => envB j (θ (Sum.inl ())))

/-- Row C: `max_{1≤j≤m} z_j`. -/
noncomputable def envRowC (m : ℕ) (θ : EnvCoord m → ℝ) : ℝ := ⨆ i : Fin m, θ (Sum.inr i)

/-- The three row values `(A, B, C)`. -/
noncomputable def envRows (m : ℕ) (θ : EnvCoord m → ℝ) : Fin 3 → ℝ :=
  ![envRowA m θ, envRowB m θ, envRowC m θ]

/-- The mixed response `(1 − λ) w + λ(1,1,1)/3`. -/
noncomputable def mixResponse (lam : ℝ) (w : Fin 3 → ℝ) : Fin 3 → ℝ := fun i => (1 - lam) * w i + lam / 3

/-- The Bellman score (1) of action `a` in the envelope family mixed with weight `λ`
(`λ = 0`: unmixed): `+` has response `(1,0,0)` and reward `−γ/2`, `−` has `(0,1,0)` and `0`,
both mixed. -/
noncomputable def envScore (m : ℕ) (γ lam : ℝ) (a : Bool) (θ : EnvCoord m → ℝ) : ℝ :=
  if a then bellmanScore γ ((1 - lam) * (-γ / 2)) (mixResponse lam ![1, 0, 0]) (envRows m θ)
  else bellmanScore γ ((1 - lam) * 0) (mixResponse lam ![0, 1, 0]) (envRows m θ)

/-- The decision loss (3) of the (mixed) envelope family. -/
noncomputable def envLoss (m : ℕ) (γ lam : ℝ) (a : Bool) (θ : EnvCoord m → ℝ) : ℝ :=
  max (envScore m γ lam true θ) (envScore m γ lam false θ) - envScore m γ lam a θ

/-- The raw site `z_j + b_j(s)` (`0 ≤ j ≤ m+1`). -/
noncomputable def envSiteA (m : ℕ) (j : Fin (m + 2)) : AffQuery (EnvCoord m) :=
  (Sum.elim (fun _ => 2 * (j : ℝ)) (fun i => if (i : ℕ) + 1 = (j : ℕ) then 1 else 0), -((j : ℝ) ^ 2))

/-- The raw site `b_j(s)` (`0 ≤ j ≤ m+1`). -/
noncomputable def envSiteB (m : ℕ) (j : Fin (m + 2)) : AffQuery (EnvCoord m) :=
  (Sum.elim (fun _ => 2 * (j : ℝ)) (fun _ => 0), -((j : ℝ) ^ 2))

/-- The raw site `z_{i+1}` of row C. -/
noncomputable def envSiteC (m : ℕ) (i : Fin m) : AffQuery (EnvCoord m) :=
  (Sum.elim (fun _ => 0) (fun i' => if i' = i then 1 else 0), 0)

/-- The raw dictionary of the envelope family: the affine expressions inside the three maxima. -/
noncomputable def envDictionary (m : ℕ) : Set (AffQuery (EnvCoord m)) :=
  Set.range (envSiteA m) ∪ Set.range (envSiteB m) ∪ Set.range (envSiteC m)

end DeepQOperator.Supplement


