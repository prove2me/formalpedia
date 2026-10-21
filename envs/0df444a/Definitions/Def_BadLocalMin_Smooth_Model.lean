-- Prove2me | Definitions.Def_BadLocalMin_Smooth_Model
-- name    : BadLocalMin_Smooth_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:23.148413+00:00
-- url     : https://prove2.me/theorems/dc1d98df-6d82-4176-9888-0d0b5008ae58
-- title:
--   §3, pp. 10–11, and Assumptions 1–2, p. 12 — deep fully connected network, squared training loss, data and activation assumptions, construction conditions (19), (23)
-- statement:
--   This file fixes the network model of Ding, Li and Sun together with the assumptions and the construction conditions used in the proof of their Theorem 1.
--
--   **Network.** A fully connected network has $H$ hidden layers; layer $h$ has $d_h$ neurons for $1 \le h \le H$, the input has $d_0$ coordinates and the output $d_{H+1}$. The parameters are
--   $$\Theta = (W_1, \mathbf b_1, W_2, \mathbf b_2, \dots, W_H, \mathbf b_H, W_{H+1}),\qquad W_h \in \mathbb R^{d_h \times d_{h-1}},\ \mathbf b_h \in \mathbb R^{d_h}.$$
--   Given the data matrix $X \in \mathbb R^{d_0 \times N}$ (one sample per column) and an activation $\sigma : \mathbb R \to \mathbb R$, the post-activations are $T_0 = X$ and, for $1 \le h \le H$,
--   $$(T_h)_{i,n} = \sigma\Big(\sum_{j=1}^{d_{h-1}} w_{h,i,j}\,(T_{h-1})_{j,n} + b_{h,i}\Big),$$
--   and the output is $T_{H+1} = W_{H+1} T_H$, with no output bias. For targets $Y \in \mathbb R^{d_{H+1} \times N}$ the empirical loss is $E(\Theta) = \|Y - T_{H+1}(\Theta)\|_F^2$.
--
--   **Intermediate configuration.** For two configurations $\Theta, \Theta'$, the configuration $\tilde\Theta'$ takes the first-layer weights $W_1$ from $\Theta$ and every other weight and bias from $\Theta'$.
--
--   **Assumption 1.** (a) $d_0^2/2 + 3d_0/2 < N$; (b) the vectors $\mathbf 1_N$, $X(i,:)$ for $1 \le i \le d_0$, and $X(i,:) \circ X(j,:)$ for $1 \le i \le j \le d_0$ (Hadamard products, each unordered pair once) are linearly independent in $\mathbb R^N$.
--
--   **Assumption 2.** There are $a \in \mathbb R$ and $\delta > 0$ such that $\sigma$ is twice continuously differentiable on $[a-\delta, a+\delta]$ and $\sigma(a), \sigma'(a), \sigma''(a)$ are all nonzero.
--
--   **Conditions (19).** $W_1 = \mathbf 0$ (19a); $\mathbf b_1 = a \cdot \mathbf 1_{d_1}$ (19b); for $2 \le h \le H$, $w_{h,i,j} > 0$ (19c) and $b_{h,i} = a - \sigma(a)\sum_{j} w_{h,i,j}$ (19d); $W_{H+1} = \frac{1}{d_H}\mathbf 1_{d_{H+1}\times d_H}$ (19e).
--
--   **Conditions (23).** For a sign factor $\kappa$ (in the paper $\kappa = [\sigma'(a)]^{H-1}\sigma''(a)$), every row $\Delta Y(i,:)$ of $\Delta Y \in \mathbb R^{m \times N}$ satisfies, for all $j \ne j'$,
--   $$\langle \Delta Y(i,:), \mathbf 1\rangle = 0,\quad \langle \Delta Y(i,:), X(j,:)\rangle = 0,\quad \langle \Delta Y(i,:), X(j,:)\circ X(j',:)\rangle = 0,\quad \kappa\,\langle \Delta Y(i,:), X(j,:)\circ X(j,:)\rangle > 0.$$
--
--   These objects are shared by every statement of the mission: the goal theorem is about `loss`, and the milestones are about the constructed configuration (19) and the output data (23).
--
--   **Formalization Note.** Indices are 0-based: the paper's neuron $i$ is Lean's `i.val + 1`, and `θ.1 k`, `θ.2 k` are $W_{k+1}$, $\mathbf b_{k+1}$. Matrices are functions `Fin a → Fin b → ℝ`; the parameter space is a finite product of real coordinates with its sup-norm metric. Assumption 1(a) is written over ℕ as $d_0^2 + 3d_0 < 2N$. Assumption 2(a) "twice differentiable" is read as $C^2$ on the interval (the paper's gloss on p. 12 says "continuous and non-zero derivatives up to the second order", and the proof uses continuity of $\sigma''$ at $a$); $\sigma'(a)$, $\sigma''(a)$ are the ordinary derivatives, $a$ being interior. $\sigma$ is arbitrary outside the interval. The printed (2b) feeds the pre-activation $z_{h-1,j}$; the formalization uses the post-activation $t_{h-1,j}$, as (3), (4) and the whole proof do.
-- source:
--   Ding, Li & Sun, arXiv:1911.01413v3, pp. 10–12 (§3, eqs. (2)–(11); Assumptions 1–2), p. 19 (eqs. (19a)–(19e), (23a)–(23d)), p. 20 (eq. (30))

import Mathlib

namespace BadLocalMin.Smooth

/-- The parameter vector Θ = (W₁, b₁, W₂, b₂, …, W_H, b_H, W_{H+1}) of eq. (10).
Widths: `d 0` is the input width d₀, `d h` (1 ≤ h ≤ H) the width of hidden layer h, and
`d (H + 1)` the output width d_{H+1}. `θ.1 k` is the weight matrix W_{k+1}
(entry `θ.1 k i j` = w_{k+1,i+1,j+1}), for k = 0, …, H; `θ.2 k` is the bias vector b_{k+1},
for k = 0, …, H − 1. The output layer has no bias. -/
abbrev Params (d : ℕ → ℕ) (H : ℕ) : Type :=
  ((k : Fin (H + 1)) → Fin (d (k.val + 1)) → Fin (d k.val) → ℝ) ×
  ((k : Fin H) → Fin (d (k.val + 1)) → ℝ)

/-- Post-activations on the N samples, eqs. (2)–(3): `post σ X θ 0 _ = X` (T₀ = X), and for
1 ≤ k + 1 ≤ H, `post σ X θ (k + 1) _ i n = σ (∑ⱼ w_{k+1,i,j} · t_{k,j,n} + b_{k+1,i})`. -/
noncomputable def post (σ : ℝ → ℝ) {d : ℕ → ℕ} {H N : ℕ} (X : Fin (d 0) → Fin N → ℝ)
    (θ : Params d H) : (k : ℕ) → k ≤ H → Fin (d k) → Fin N → ℝ
  | 0, _ => X
  | k + 1, hk => fun i n =>
      σ ((∑ j, θ.1 ⟨k, by omega⟩ i j * post σ X θ k (by omega) j n) + θ.2 ⟨k, by omega⟩ i)

/-- The network output T_{H+1} = W_{H+1} T_H, eq. (4) (no output bias). -/
noncomputable def output (σ : ℝ → ℝ) {d : ℕ → ℕ} {H N : ℕ} (X : Fin (d 0) → Fin N → ℝ)
    (θ : Params d H) : Fin (d (H + 1)) → Fin N → ℝ :=
  fun i n => ∑ j, θ.1 (Fin.last H) i j * post σ X θ H le_rfl j n

/-- The empirical squared loss E(Θ) = ‖Y − T_{H+1}(Θ)‖²_F, eq. (11). -/
noncomputable def loss (σ : ℝ → ℝ) {d : ℕ → ℕ} {H N : ℕ} (X : Fin (d 0) → Fin N → ℝ)
    (Y : Fin (d (H + 1)) → Fin N → ℝ) (θ : Params d H) : ℝ :=
  ∑ i, ∑ n, (Y i n - output σ X θ i n) ^ 2

/-- The intermediate configuration Θ̃′ of eq. (30): the first-layer weights W₁ are taken from
Θ, all other weights and all biases from Θ′. -/
def tilde {d : ℕ → ℕ} {H : ℕ} (θ θ' : Params d H) : Params d H :=
  (Function.update θ'.1 0 (θ.1 0), θ'.2)

/-- The vectors of the set 𝒳 in eq. (12): the all-ones vector 1_N (`none`), the rows X(i,:)
(`some (inl i)`), and the Hadamard products X(i,:) ∘ X(j,:) for unordered pairs, indexed by
i ≤ j (`some (inr ⟨(i, j), _⟩)`). -/
def features {d0 N : ℕ} (X : Fin d0 → Fin N → ℝ) :
    Option (Fin d0 ⊕ {p : Fin d0 × Fin d0 // p.1 ≤ p.2}) → Fin N → ℝ
  | none => fun _ => 1
  | some (Sum.inl i) => X i
  | some (Sum.inr p) => fun n => X p.1.1 n * X p.1.2 n

/-- Assumption 1 (p. 12): (a) d₀²/2 + 3d₀/2 < N, written over ℕ as d₀² + 3d₀ < 2N;
(b) the vectors of 𝒳 are linearly independent. -/
def Assumption1 {d0 N : ℕ} (X : Fin d0 → Fin N → ℝ) : Prop :=
  d0 * d0 + 3 * d0 < 2 * N ∧ LinearIndependent ℝ (features X)

/-- Assumption 2 (p. 12) at a given point a and radius δ: δ > 0, σ is twice continuously
differentiable on [a − δ, a + δ], and σ(a), σ′(a), σ″(a) are all nonzero. -/
def Assumption2At (σ : ℝ → ℝ) (a δ : ℝ) : Prop :=
  0 < δ ∧ ContDiffOn ℝ 2 σ (Set.Icc (a - δ) (a + δ)) ∧
    σ a ≠ 0 ∧ deriv σ a ≠ 0 ∧ deriv (deriv σ) a ≠ 0

/-- Assumption 2 (p. 12): there exist a ∈ ℝ and δ > 0 at which `Assumption2At` holds. -/
def Assumption2 (σ : ℝ → ℝ) : Prop :=
  ∃ a δ : ℝ, Assumption2At σ a δ

/-- Conditions (19a)–(19d) on the hidden layers (p. 19): W₁ = 0 (19a); b₁ = a · 1 (19b); and
for 2 ≤ h ≤ H (Lean index k = h − 1): w_{h,i,j} > 0 (19c) and
b_{h,i} = a − σ(a) ∑ⱼ w_{h,i,j} (19d). -/
def Constr19ad (σ : ℝ → ℝ) (a : ℝ) {d : ℕ → ℕ} {H : ℕ} (θ : Params d H) : Prop :=
  (∀ i j, θ.1 ⟨0, Nat.succ_pos H⟩ i j = 0) ∧
  (∀ (hH : 0 < H) i, θ.2 ⟨0, hH⟩ i = a) ∧
  (∀ (k : ℕ) (hk : k < H), 1 ≤ k → ∀ i : Fin (d (k + 1)),
    (∀ j : Fin (d k), 0 < θ.1 ⟨k, by omega⟩ i j) ∧
    θ.2 ⟨k, hk⟩ i = a - σ a * ∑ j, θ.1 ⟨k, by omega⟩ i j)

/-- Condition (19e) on the output layer (p. 19): W_{H+1} = (1/d_H) · 1_{d_{H+1} × d_H}. -/
def Constr19e {d : ℕ → ℕ} {H : ℕ} (θ : Params d H) : Prop :=
  ∀ i j, θ.1 (Fin.last H) i j = 1 / (d H : ℝ)

/-- Conditions (23a)–(23d) on the rows of ΔY (p. 19), with sign factor κ (in the paper
κ = [σ′(a)]^{H−1} σ″(a)): for every row i and all j ≠ j′,
⟨ΔY(i,:), 1⟩ = 0, ⟨ΔY(i,:), X(j,:)⟩ = 0, ⟨ΔY(i,:), X(j,:) ∘ X(j′,:)⟩ = 0, and
κ ⟨ΔY(i,:), X(j,:) ∘ X(j,:)⟩ > 0. -/
def Cond23 {d0 m N : ℕ} (X : Fin d0 → Fin N → ℝ) (κ : ℝ) (dY : Fin m → Fin N → ℝ) : Prop :=
  ∀ i, (∑ n, dY i n = 0) ∧ (∀ j, ∑ n, dY i n * X j n = 0) ∧
    (∀ j j', j ≠ j' → ∑ n, dY i n * (X j n * X j' n) = 0) ∧
    (∀ j, 0 < κ * ∑ n, dY i n * (X j n * X j n))

end BadLocalMin.Smooth


