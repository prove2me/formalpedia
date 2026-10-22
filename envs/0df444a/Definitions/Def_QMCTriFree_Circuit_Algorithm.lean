-- Prove2me | Definitions.Def_QMCTriFree_Circuit_Algorithm
-- name    : QMCTriFree_Circuit_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:45.141726+00:00
-- url     : https://prove2.me/theorems/0921c324-d936-48aa-97b2-56972cca2265
-- title:
--   Algorithm 17: GP rounding, equatorial $P_k$, signs $\varepsilon_{ij}$, the commuting circuit, $f$, $F(\beta;x)$, $\theta_{ij}$ and the expected output energy (pp. 8, 10–12, 16–17)
-- statement:
--   A single-qubit state is described by its **Bloch vector** $\vec v\in\mathbb R^3$, $\|\vec v\|=1$, through $|v\rangle\langle v|=\tfrac12(1+\vec v\cdot\vec\sigma)$ with $\vec\sigma=(X,Y,Z)$; a product state $\bigotimes_k|v_k\rangle$ has density matrix $\bigotimes_k\tfrac12(1+\vec v_k\cdot\vec\sigma)$, and $E_{ij}=\tfrac12(1-\vec v_i\cdot\vec v_j)$ (eq. (8)).
--
--   **GP rounding.** Given a solution $M$ of $\mathrm{Lasserre}_2(H)$, let $W_{k\sigma}\in\mathbb R^D$ ($k\in V$, $\sigma\in\{X,Y,Z\}$) be Gram vectors of its $\mathcal P^{(1)}_n$ block, $\langle W_{k\sigma},W_{l\tau}\rangle=M(\sigma_k,\tau_l)$. Draw a $3\times 3D$ matrix $Z$ of independent standard Gaussians and set
--   $$\vec v_k=\frac{Z u_k}{\|Z u_k\|},\qquad u_k=(W_{kX},W_{kY},W_{kZ}).$$
--
--   **Equatorial Paulis and signs.** Independently of $Z$, draw independent standard Gaussians $g_k\in\mathbb R^3$ and set $\vec n_k=$ the normalisation of $g_k-(g_k\cdot\vec v_k)\vec v_k$, a uniformly random unit vector orthogonal to $\vec v_k$, and $P_k=\vec n_k\cdot\vec\sigma_k$. For an edge $(k,l)$ let $z_{kl}=\langle v_k|P_l|v_l\rangle\langle v_l|P_k|v_k\rangle=\operatorname{Tr}(\rho_kP_l\rho_lP_k)$ and $\varepsilon_{kl}=+1$ if $\arg z_{kl}\in[0,\pi)$, $\varepsilon_{kl}=-1$ otherwise (rule (10)).
--
--   **Circuit.** For angles $\theta_{kl}$ the circuit is $U=\prod_{k<l,\ w_{kl}\ne0}\exp(i\varepsilon_{kl}\theta_{kl}P_k\otimes P_l)$, each gate written as $\cos\theta_{kl}\,1+i\varepsilon_{kl}\sin\theta_{kl}\,P_kP_l$, and the output state is $\rho_{\mathrm{out}}=U\bigl(\bigotimes_k|v_k\rangle\langle v_k|\bigr)U^\dagger$. For a fixed product state, $\langle h_{ij}\rangle$ denotes the expectation of $\operatorname{Tr}(h_{ij}\rho_{\mathrm{out}})$ over the draws $g$.
--
--   **Functions and angles.** With ${}_2F_1$ the Gauss hypergeometric function,
--   $$f(x)=\tfrac12-\tfrac{4}{3\pi}\Bigl(-\tfrac{1+2x}{3}\Bigr)\,{}_2F_1\Bigl(\tfrac12,\tfrac12;\tfrac52;\bigl(-\tfrac{1+2x}{3}\bigr)^2\Bigr),$$
--   $$F(\beta;x)=f(x)\Bigl(\tfrac12+\tfrac12\bigl(1-\beta^2(1-x)^2\bigr)+\tfrac2\pi\beta x\bigl(\sqrt{1-\beta^2}+(1-\sqrt{1-\beta^2})x\bigr)\Bigr),$$
--   and $\theta_{ij}=\tfrac12\arcsin(\beta x_{ij})$ if $x_{ij}\ge0$, $\theta_{ij}=0$ otherwise. The **expected output energy** $E$ of Algorithm 17 with parameter $\beta$ is the expectation of $\operatorname{Tr}(H\rho_{\mathrm{out}})$ over $Z$ and $g$ jointly.
--
--   This is Algorithm 17 written out; every random object is a function of $M$, the Gram vectors and the two independent Gaussian draws.
--
--   **Formalization Note** The paper defines GP rounding only by citation to Gharibian–Parekh; the Gaussian projection above is a reconstruction which reproduces the paper's eq. (12) exactly (the factor $1/\sqrt3$ making $u_k$ a unit vector cancels in the normalisation). Every Gram factorisation $W$ gives the same law of $(\vec v_k)$. The uniform equator draw is represented by a projected normalised Gaussian. Vectors in $\mathbb R^3$ are `Fin 3 → ℝ`; normalising the zero vector returns zero (a null event). The sign uses Mathlib's `Complex.arg` with values in $(-\pi,\pi]$; the rule agrees with the paper's partition $[0,\pi)\cup[-\pi,0)$, negative reals receiving $-1$ in both. Gates are applied in lexicographic edge order; they commute. ${}_2F_1$ is Mathlib's `ordinaryHypergeometric`, a convergent series for arguments in $[0,1]$. The expectation is a Bochner integral over the product of the Gaussian laws.
-- source:
--   King, An Improved Approximation Algorithm for Quantum Max-Cut on Triangle-Free Graphs, arXiv:2209.02589v3, p. 8 (Bloch vectors), pp. 10–11 (eq. (8), the random P_k, rule (10)), p. 12 (Section 6, eq. (12)), p. 16 (Algorithm 17, eq. (15)), p. 17 (eq. (16))

import Mathlib
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Definitions.Def_QMCTriFree_Circuit_Lasserre

set_option autoImplicit false

namespace QMCTriFree.Circuit

open QMCProduct.HalfApprox Matrix MeasureTheory ProbabilityTheory

/-! King, arXiv:2209.02589v3: product states and Bloch vectors (pp. 8, 10), GP rounding
(Section 6, p. 12), the equatorial `P_k`, the signs `ε_ij` and the commuting circuit (Section 5.2,
pp. 10–11; Algorithm 17, p. 16), and the functions `f`, `F` and the angles `θ_ij`
((12), p. 12; (15)–(16), pp. 16–17). Real 3-vectors are `Fin 3 → ℝ` with the dot product;
coordinate `a` pairs with the Pauli `pauli1 a.succ` (`X, Y, Z`). -/

/-- `u / ‖u‖` (the zero vector is sent to itself; this happens on null events only). -/
noncomputable def normalize (u : Fin 3 → ℝ) : Fin 3 → ℝ := (Real.sqrt (u ⬝ᵥ u))⁻¹ • u

/-- `u⃗ · σ⃗ = u_x X + u_y Y + u_z Z`. -/
noncomputable def pauliVec (u : Fin 3 → ℝ) : Matrix Bool Bool ℂ :=
  ∑ a : Fin 3, (u a : ℂ) • pauli1 a.succ

/-- The single-qubit state with Bloch vector `v⃗`: `|v⟩⟨v| = ½(1 + v⃗ · σ⃗)`, p. 8. -/
noncomputable def rho1 (v : Fin 3 → ℝ) : Matrix Bool Bool ℂ := (1 / 2 : ℂ) • (1 + pauliVec v)

/-- The product state `⊗_k |v_k⟩⟨v_k|`. -/
noncomputable def rho0 {n : ℕ} (v : Fin n → Fin 3 → ℝ) : Op n :=
  QAlgorithms.kronAll (fun k => rho1 (v k))

/-- The product-state edge energy (8), p. 10: `E_ij = ½(1 − v⃗_i · v⃗_j)`. -/
noncomputable def Eij {n : ℕ} (v : Fin n → Fin 3 → ℝ) (i j : Fin n) : ℝ :=
  (1 / 2 : ℝ) * (1 - v i ⬝ᵥ v j)

/-- The energy `Tr(A ρ)` (real part) of an operator `A` in a state `ρ`. -/
noncomputable def energy {n : ℕ} (A ρ : Op n) : ℝ := (A * ρ).trace.re

/-- Standard Gaussian law on `Fin m → ℝ` (independent `N(0,1)` coordinates). -/
noncomputable def gaussVec (m : ℕ) : Measure (Fin m → ℝ) :=
  Measure.pi (fun _ : Fin m => gaussianReal 0 1)

/-! ### GP rounding (Algorithm 17, step 2; reconstruction recorded in the description) -/

/-- `W` is a Gram factorisation of the `P_n^(1)` block of `M`: for vertices `k, l` and Paulis
`σ, τ ∈ {X, Y, Z}`, `∑_c W_{kσ}(c) W_{lτ}(c) = M(σ_k, τ_l)`. -/
def IsGramOfBlock {n D : ℕ} (M : Matrix (P2 n) (P2 n) ℝ) (W : Fin n → Fin 3 → Fin D → ℝ) : Prop :=
  ∀ k l : Fin n, ∀ σ τ : Fin 3,
    ∑ c : Fin D, W k σ c * W l τ c = entry M (siteStr σ.succ k) (siteStr τ.succ l)

/-- The Gaussian `3 × (3D)` rounding matrix: independent `N(0,1)` entries `Z_{a,(σ,c)}`. -/
noncomputable def gaussZ (D : ℕ) : Measure (Fin 3 → Fin 3 → Fin D → ℝ) :=
  Measure.pi (fun _ : Fin 3 => Measure.pi (fun _ : Fin 3 => gaussVec D))

/-- GP rounding: `v⃗_k = Z u_k / ‖Z u_k‖` where `u_k` is the concatenation
`(W_{kX}, W_{kY}, W_{kZ})` (the factor `1/√3` making `u_k` a unit vector cancels). -/
noncomputable def gpBloch {n D : ℕ} (W : Fin n → Fin 3 → Fin D → ℝ)
    (Z : Fin 3 → Fin 3 → Fin D → ℝ) (k : Fin n) : Fin 3 → ℝ :=
  normalize (fun a => ∑ σ : Fin 3, ∑ c : Fin D, Z a σ c * W k σ c)

/-! ### The random equatorial `P_k`, the signs and the circuit -/

/-- Law of the equator draws: one independent standard Gaussian `g_k ∈ ℝ³` per vertex. -/
noncomputable def gaussG (n : ℕ) : Measure (Fin n → Fin 3 → ℝ) :=
  Measure.pi (fun _ : Fin n => gaussVec 3)

/-- `n⃗_k = normalize(g_k − (g_k · v⃗_k) v⃗_k)`; for a unit `v⃗_k` and Gaussian `g_k` it is uniform on
the equator `{n⃗ ∈ S² : n⃗ · v⃗_k = 0}` (Algorithm 17, step 7). -/
noncomputable def equator {n : ℕ} (v : Fin n → Fin 3 → ℝ) (g : Fin n → Fin 3 → ℝ) (k : Fin n) :
    Fin 3 → ℝ :=
  normalize (g k - (g k ⬝ᵥ v k) • v k)

/-- `⟨v_k|P_l|v_l⟩⟨v_l|P_k|v_k⟩ = Tr(ρ_k P_l ρ_l P_k)` with `P = n⃗ · σ⃗` (phase free). -/
noncomputable def zval {n : ℕ} (v nv : Fin n → Fin 3 → ℝ) (k l : Fin n) : ℂ :=
  (rho1 (v k) * pauliVec (nv l) * rho1 (v l) * pauliVec (nv k)).trace

/-- The sign rule (10) / Algorithm 17, step 9: `ε = +1` if `arg z ∈ [0, π)`, `ε = −1` otherwise
(Mathlib's `Complex.arg` takes values in `(−π, π]`). -/
noncomputable def sgn (z : ℂ) : ℝ :=
  if 0 ≤ Complex.arg z ∧ Complex.arg z < Real.pi then 1 else -1

/-- The single-qubit matrix `A` on qubit `k`, identity elsewhere. -/
noncomputable def embed {n : ℕ} (k : Fin n) (A : Matrix Bool Bool ℂ) : Op n :=
  QAlgorithms.kronAll (fun q => if q = k then A else 1)

/-- The gate `exp(i ε θ P_k ⊗ P_l) = cos θ · 1 + i ε sin θ · P_k P_l` (valid as `(P_k P_l)² = 1`). -/
noncomputable def gate {n : ℕ} (nv : Fin n → Fin 3 → ℝ) (ε θ : ℝ) (k l : Fin n) : Op n :=
  (Real.cos θ : ℂ) • 1 +
    (Complex.I * ((ε * Real.sin θ : ℝ) : ℂ)) • (embed k (pauliVec (nv k)) * embed l (pauliVec (nv l)))

/-- The edges `(k, l)`, `k < l`, `w_kl ≠ 0`, in lexicographic order. -/
noncomputable def edgeList {n : ℕ} (w : Fin n → Fin n → ℝ) : List (Fin n × Fin n) := by
  classical
  exact (List.finRange n).flatMap fun k =>
    ((List.finRange n).filter fun l => decide (k < l ∧ w k l ≠ 0)).map fun l => (k, l)

/-- The circuit `∏_kl exp(i ε_kl θ_kl P_k ⊗ P_l)` over the edges, signs by rule (10). -/
noncomputable def circuit {n : ℕ} (w : Fin n → Fin n → ℝ) (θ : Fin n → Fin n → ℝ)
    (v nv : Fin n → Fin 3 → ℝ) : Op n :=
  ((edgeList w).map fun e => gate nv (sgn (zval v nv e.1 e.2)) (θ e.1 e.2) e.1 e.2).prod

/-- The output state `U (⊗_k |v_k⟩⟨v_k|) U†`. -/
noncomputable def outState {n : ℕ} (w : Fin n → Fin n → ℝ) (θ : Fin n → Fin n → ℝ)
    (v nv : Fin n → Fin 3 → ℝ) : Op n :=
  circuit w θ v nv * rho0 v * (circuit w θ v nv)ᴴ

/-- The expected energy on `h_ij` of the circuit state for a fixed product state `v`, averaged
over the equator draws (the `⟨h_ij⟩` of Lemmas 12 and 18). -/
noncomputable def avgEdgeEnergy {n : ℕ} (w : Fin n → Fin n → ℝ) (θ : Fin n → Fin n → ℝ)
    (v : Fin n → Fin 3 → ℝ) (i j : Fin n) : ℝ :=
  ∫ g, energy (hEdge i j) (outState w θ v (equator v g)) ∂(gaussG n)

/-! ### The functions `f`, `F`, the angles, and the output energy of Algorithm 17 -/

/-- (12), p. 12: `f(x) = ½ − (4/(3π)) t ₂F₁(½, ½; 5/2; t²)` with `t = −(1 + 2x)/3`. -/
noncomputable def fGP (x : ℝ) : ℝ :=
  1 / 2 - 4 / (3 * Real.pi) * (-(1 + 2 * x) / 3) *
    ordinaryHypergeometric (1 / 2 : ℝ) (1 / 2 : ℝ) (5 / 2 : ℝ) ((-(1 + 2 * x) / 3) ^ 2)

/-- The bracket of (17), p. 17:
`½ + ½(1 − β²(1 − x)²) + (2/π) β x (√(1 − β²) + (1 − √(1 − β²)) x)`. -/
noncomputable def bracket (β x : ℝ) : ℝ :=
  1 / 2 + 1 / 2 * (1 - β ^ 2 * (1 - x) ^ 2) +
    2 / Real.pi * β * x * (Real.sqrt (1 - β ^ 2) + (1 - Real.sqrt (1 - β ^ 2)) * x)

/-- Algorithm 17, step 4: `F(β; x) = f(x) · bracket(β, x)`. -/
noncomputable def Fβ (β x : ℝ) : ℝ := fGP x * bracket β x

/-- (15)/(16): `θ_ij = ½ arcsin(β x_ij)` if `x_ij ≥ 0`, else `0`. -/
noncomputable def thetaOf {n : ℕ} (β : ℝ) (M : Matrix (P2 n) (P2 n) ℝ) (i j : Fin n) : ℝ :=
  if 0 ≤ xval M i j then (1 / 2 : ℝ) * Real.arcsin (β * xval M i j) else 0

/-- The expected output energy `E` of Algorithm 17 with parameter `β`, run on `M` with Gram
factorisation `W`: the energy `Tr(H ρ_out)` averaged over the rounding matrix and the equator
draws (independent). -/
noncomputable def algEnergy {n D : ℕ} (w : Fin n → Fin n → ℝ) (M : Matrix (P2 n) (P2 n) ℝ)
    (W : Fin n → Fin 3 → Fin D → ℝ) (β : ℝ) : ℝ :=
  ∫ p, energy (qmcH w)
      (outState w (thetaOf β M) (gpBloch W p.1) (equator (gpBloch W p.1) p.2))
    ∂((gaussZ D).prod (gaussG n))

end QMCTriFree.Circuit


