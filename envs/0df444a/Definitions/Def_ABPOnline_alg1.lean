-- Prove2me | Definitions.Def_ABPOnline_alg1
-- name    : ABPOnline_alg1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:56:02.094754+00:00
-- url     : https://prove2.me/theorems/bf990be6-96c3-4df3-9259-7969e8690ea2
-- title:
--   Algorithm 1 (OnlinePerceptron)
-- statement:
--   Parameters: a rational $T\in(0,1)$, a target $a$, a simple predictable control $\beta$ on $[0,T]$, and the final-block feedback $v_N$ (for budget $c_F$ and an even $p>4$). Input: $M$, $N$ and the columns $g_1,\dots,g_N$, revealed one at a time. Put $k_0=\lfloor TN\rfloor$, $h_N=(N-k_0)/N$, $X=B=0\in\mathbb R^M$.
--
--   1. **Stage I**, $k=1,\dots,k_0$: evaluate $\beta$ coordinatewise from the stored Brownian mesh values (every block and observation time of its representation rounded down to the $1/N$ mesh) to get $q^{\mathrm{raw}}$; $q\leftarrow\Pi_N(q^{\mathrm{raw}})$; observe $g_k$, $Z\leftarrow g_k/\sqrt N$; $(\sigma_k,\Delta B)\leftarrow\mathrm{Steer}_N(q,Z)$; $X\leftarrow X+\sigma_kZ$, $B\leftarrow B+\Delta B$.
--   2. **Stage II**: $q^{\det}_i\leftarrow(a-X_i)_+/h_N$, $\hat Z\leftarrow0$; for $\ell=0,\dots,N-k_0-1$: $\hat a_i\leftarrow v_N(\ell/N,\hat Z_i)$; $q\leftarrow\Pi_N(q^{\det}+\hat a)$; observe $g_{k_0+\ell+1}$, $Z\leftarrow g_{k_0+\ell+1}/\sqrt N$; $(\sigma_{k_0+\ell+1},\Delta B)\leftarrow\mathrm{Steer}_N(q,Z)$; $X\leftarrow X+\sigma_{k_0+\ell+1}Z$; $\hat Z\leftarrow\hat Z+\hat a/N+\Delta B$.
--
--   Output: $\sigma_1,\dots,\sigma_N$.
--
--   This is the online algorithm of Propositions 4.7 and 4.8.
--
--   **Formalization Note** The algorithm is a function of the matrix; the sign for column $k$ is computed from the state after columns $0,\dots,k-1$ and column $k$, so it is online by construction. Stage I's step $k+1$ covers $(k/N,(k+1)/N]$ and uses block $j$ when $\lfloor Ns_j\rfloor\le k<\lfloor Ns_{j+1}\rfloor$, reading $B_r$ as the mesh value with index $\lfloor Nr\rfloor$ (the paper's rounding rule). The feedback is `v N (N - k₀)`, i.e. $v_N$ for $L_N=N-k_0$. All mesh values are stored, which gives the same output as storing only the required ones.
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), Algorithm 1, p.14 (PDF p.15), with the evaluation rule for $eta$ on pp.13–14

import Mathlib
import Definitions.Def_ABPOnline_steerSign
import Definitions.Def_ABPOnline_SimpleCtrl

set_option autoImplicit false

namespace ABPOnline

/-- The working state of Algorithm 1 (arXiv:2609.02124, printed p.14, PDF p.15): the margin
vector `X`, the Brownian mesh values `B̂_0, B̂_1, …` produced by the steering map in Stage I, the
deterministic Stage II drift `q^det`, and the Stage II Euler state `Ẑ`. -/
structure Alg1State (M : ℕ) where
  X : Fin M → ℝ
  Bm : ℕ → Fin M → ℝ
  qdet : Fin M → ℝ
  Zh : Fin M → ℝ

/-- The initial state: `X = B = 0`. -/
def Alg1State.init (M : ℕ) : Alg1State M := ⟨0, fun _ => 0, 0, 0⟩

/-- The Stage I control `q^raw` at step index `k` (the paper's step `k+1`, time interval
`(k/N, (k+1)/N]`): `β` evaluated coordinatewise from the stored Brownian mesh values, every block
time and observation time of its representation rounded down to the `1/N` mesh
(arXiv:2609.02124, p.13–14 and line 3 of Algorithm 1). Block `j` is active when
`⌊N s_j⌋ ≤ k < ⌊N s_{j+1}⌋`, and `B_{r}` is read as `B̂_{⌊N r⌋}`. -/
noncomputable def stage1Control {M : ℕ} (β : SimpleCtrl) (N k : ℕ) (Bm : ℕ → Fin M → ℝ) :
    Fin M → ℝ :=
  fun i => ∑ j ∈ Finset.range β.L,
    if ⌊(N : ℝ) * (β.s j : ℝ)⌋₊ ≤ k ∧ k < ⌊(N : ℝ) * (β.s (j + 1) : ℝ)⌋₊ then
      β.F j (fun ℓ => Bm ⌊(N : ℝ) * (β.r j ℓ : ℝ)⌋₊ i) else 0

/-- One iteration of Algorithm 1 (OnlinePerceptron) at step index `k` (0-based; it processes the
paper's column `g_{k+1}`), given the state before the column and the column `g ∈ ℝ^M`. Returns the
sign and the new state. Stage I (`k < k₀ = ⌊TN⌋`, lines 2–9) and Stage II (lines 10–18, with
`ℓ = k − k₀`; at `k = k₀` the drift `q^det_i = (a − X_i)_+/h_N` is set and `Ẑ = 0`). The steering
step `Steer_N(q, Z)` is `steerSign`/`steerInnov` with the drift `b = q/N`. The final-block feedback
is `v N L_N` with `L_N = N − k₀` and `h_N = L_N/N`. -/
noncomputable def alg1Step (T : ℚ) (a : ℝ) (β : SimpleCtrl) (v : ℕ → ℕ → ℝ → ℝ → ℝ)
    {M : ℕ} (N k : ℕ) (st : Alg1State M) (g : Fin M → ℝ) : ℝ × Alg1State M :=
  let k0 := ⌊(T : ℝ) * N⌋₊
  let hN : ℝ := ((N - k0 : ℕ) : ℝ) / N
  let Z := (Real.sqrt N)⁻¹ • g
  if k < k0 then
    let q := projN N (stage1Control β N k st.Bm)
    let b := (N : ℝ)⁻¹ • q
    let σ := steerSign N b Z
    (σ, { st with X := st.X + σ • Z,
                  Bm := Function.update st.Bm (k + 1) (st.Bm k + steerInnov N b Z) })
  else
    let qdet : Fin M → ℝ := if k = k0 then fun i => max (a - st.X i) 0 / hN else st.qdet
    let Zh : Fin M → ℝ := if k = k0 then 0 else st.Zh
    let ahat : Fin M → ℝ := fun i => v N (N - k0) (((k - k0 : ℕ) : ℝ) / N) (Zh i)
    let q := projN N (qdet + ahat)
    let b := (N : ℝ)⁻¹ • q
    let σ := steerSign N b Z
    (σ, { st with X := st.X + σ • Z, qdet := qdet,
                  Zh := Zh + (N : ℝ)⁻¹ • ahat + steerInnov N b Z })

/-- Column `k` of the matrix (`0` beyond the last column). -/
def matCol {M N : ℕ} (G : Fin M × Fin N → ℝ) (k : ℕ) : Fin M → ℝ :=
  fun i => if h : k < N then G (i, ⟨k, h⟩) else 0

/-- The state of Algorithm 1 after the first `k` columns. -/
noncomputable def alg1Run (T : ℚ) (a : ℝ) (β : SimpleCtrl) (v : ℕ → ℕ → ℝ → ℝ → ℝ)
    {M N : ℕ} (G : Fin M × Fin N → ℝ) : ℕ → Alg1State M
  | 0 => Alg1State.init M
  | k + 1 => (alg1Step T a β v N k (alg1Run T a β v G k) (matCol G k)).2

/-- The signs `σ_1, …, σ_N` returned by Algorithm 1 (OnlinePerceptron) of arXiv:2609.02124
(printed p.14, PDF p.15) with parameters `T`, `a`, `β` and the final-block feedback family `v`;
`alg1 T a β v M N k G` is the sign for column `k` (0-based).

**Formalization Note** The parameter `p` of Algorithm 1 enters only through the feedback `v_N` of
Lemma 4.5, which is the parameter `v` here. The algorithm stores every mesh value of `B̂`; the
output is the same as storing only the required ones. -/
noncomputable def alg1 (T : ℚ) (a : ℝ) (β : SimpleCtrl) (v : ℕ → ℕ → ℝ → ℝ → ℝ)
    (M N : ℕ) : Fin N → (Fin M × Fin N → ℝ) → ℝ :=
  fun k G => (alg1Step T a β v N k (alg1Run T a β v G k) (matCol G k)).1

end ABPOnline


