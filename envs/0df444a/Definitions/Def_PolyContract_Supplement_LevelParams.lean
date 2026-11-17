-- Prove2me | Definitions.Def_PolyContract_Supplement_LevelParams
-- name    : PolyContract_Supplement_LevelParams
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:59:18.926201+00:00
-- url     : https://prove2.me/theorems/f3edc025-68de-4c7d-9adf-84518a528352
-- title:
--   Comb gadget: elements, rewards, curvatures, inputs $\mu_j$, and the parameter rule (Definitions C.11–C.12)
-- statement:
--   The comb gadget is built from inputs $\mu^{\mathrm{in}}\in\mathcal F$ of length $k$, with width $\delta:=1/(3\mu^{\mathrm{in}}_1)$ and $\mu_j:=\delta\mu^{\mathrm{in}}_{j+1}$ for $0\le j\le k-1$ (so $\mu_0=1/3$). Level $0$ is the base $\{C_0,C_1,C_2\}$ with $m=(5,12,4)$, $\beta=(1,4,4)$. Step $j\ge1$ adds the dummies $\tau_{1,j},\tau_{2,j}$ with reward $m^{(j)}_\delta$ and curvature $\beta^{(j)}_\delta$, and $b_j$ with reward $M_j$ and curvature $\beta^{(j)}_\delta/12$; $E_j:=E_{j-1}\cup\{\tau_{1,j},\tau_{2,j},b_j\}$. Constants: $\varepsilon_0=1/30$, $R_0=3/10$, $\iota=1/100$, $R^{(j)}_1:=1/3+\sum_{i=0}^{j}\mu_i+\varepsilon_0$.
--
--   The **parameter rule** at the step $k\to k+1$, with $\mu:=\mu_{k+1}$, $R_1:=R^{(k)}_1$, $|R|:=R_1-R_0$ and $E:=E_k\cup\{\tau_1,\tau_2\}$:
--
--   1. (P1) $M:=M_k$, $m_\delta:=M/2$, $m_*:=m_\delta+64M$;
--   2. (P2) $1/\beta_\delta:=\tfrac34\cdot8^k$, $\beta_b:=\beta_\delta/12$;
--   3. (P3) $w:=64M\mu$, $d_e:=\mu(m_*-m_e)/\beta_e$, $\bar d:=d(E_k)/d_{\tau_1}$;
--   4. (P4) $\Delta_b:=\tfrac{415}{2}M$, $m_b:=m_\delta+\Delta_b$, $s:=\tfrac{12}{13}\Delta_b$, $\bar m:=m_\delta+s$, $\psi_{k+1}:=\tfrac{12}{13}\Delta_b^2/\beta_\delta$;
--   5. (P5) $\Pi:=\sum_{e\in E_k}(m_\delta-m_e)d_e$, $\Delta F:=w/\beta_\delta+d(E_k)-(q_k\mu-\Pi)/s$;
--   6. (P6) $\bar\rho_0:=7/6$, $\bar\rho_k:=R_0m^{(k)}_\delta-\beta^{(k)}_\delta F^{(k)}_{\tau_2}$ ($k\ge1$), $a_2:=\tfrac{12}{13}(\mu-|R|/2)$, $a_0:=\beta_\delta(q_k\mu-\Pi)$, $u_0:=a_2\Delta_b-(\tfrac12+\bar d)w+a_0/\Delta_b$, $F_{\tau_2}:=(R_0m_\delta-\bar\rho_k-w+u_0-s\iota)/\beta_\delta$, $F_{\tau_1}:=F_{\tau_2}+\Delta F$;
--   7. (P7) $K:=d(E)+12F_{\tau_1}-13\,(w/2-s(R_0+R_1)/2)/\beta_\delta$;
--   8. (P8) $q_{k+1}:=q_k+\psi_{k+1}$, $p_{k+1}:=p_k+m_\delta F_{\tau_2}+(K-d(E)+F_{\tau_1})\bar m$,
--
--   with $M_0:=12$, $p_0=10$, $q_0=7$, and level $k+1$ receiving $m^{(k+1)}_\delta:=m_\delta$, $\beta^{(k+1)}_\delta:=\beta_\delta$, $M_{k+1}:=m_b$, $F^{(k+1)}_{\tau_i}:=F_{\tau_i}$, $K_{k+1}:=K$.
--
--   **Formalization Note** All levels live in one ambient type, the base elements plus triples indexed by the step; level $j$ is the finite subset $E_j$. $\mu^{\mathrm{in}}$ is a list indexed from $0$. The rewards and curvatures are explicit functions of the step index, and the numbers $p,q,F_{\tau_1},F_{\tau_2},K$ are computed by recursion on the level; the rule is trace-free, so no best response enters.
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Definition C.11, p.57 (PDF p.58); Definition C.12 and Table 1, pp.58–59 (PDF pp.59–60); Proposition C.10, p.56

import Mathlib

set_option autoImplicit false

namespace PolyContract.Supplement

/-- The elements of all levels of the comb gadget (Klimm, Lippke, Warode, arXiv:2611.04934,
version of November 3, 2026, sha256 18cfc0a5…, Definition C.11, p.57): the base elements
`C₀, C₁, C₂` (`Sum.inl 0, 1, 2`) and, for every step `j ≥ 1`, the elements `τ_{1,j}`, `τ_{2,j}`,
`b_j` (`Sum.inr (j, 0)`, `Sum.inr (j, 1)`, `Sum.inr (j, 2)`).

**Formalization Note** One ambient type holds every level; level `j` is the finite subset
`Elev j`, and the instances of a level live on that subset. The entries `Sum.inr (0, i)` belong
to no level. -/
abbrev CombU : Type := Fin 3 ⊕ (ℕ × Fin 3)

/-- The dummy `τ_{1,j}` added at step `j` (arXiv:2611.04934, Definition C.11, p.57). -/
def tau1 (j : ℕ) : CombU := Sum.inr (j, 0)

/-- The dummy `τ_{2,j}` added at step `j` (arXiv:2611.04934, Definition C.11, p.57). -/
def tau2 (j : ℕ) : CombU := Sum.inr (j, 1)

/-- The new element `b_j` added at step `j` (arXiv:2611.04934, Definition C.11, p.57). -/
def bnew (j : ℕ) : CombU := Sum.inr (j, 2)

/-- `M_k` (arXiv:2611.04934, Definition C.12, (P1), (P4), p.58): `M₀ := 12` and
`M_{k+1} := m_b = m_δ + ∆_b` with `m_δ = M_k/2` and `∆_b = (415/2) M_k`. -/
noncomputable def Mseq : ℕ → ℝ
  | 0 => 12
  | k + 1 => Mseq k / 2 + 415 / 2 * Mseq k

/-- `1/β_δ := (3/4)·8^k` at the step `k → k+1` (arXiv:2611.04934, (P2), p.58). -/
noncomputable def invβδ (k : ℕ) : ℝ := 3 / 4 * 8 ^ k

/-- `β_δ` at the step `k → k+1` (arXiv:2611.04934, (P2), p.58). -/
noncomputable def βδ (k : ℕ) : ℝ := 1 / invβδ k

/-- `β_b := β_δ/12` at the step `k → k+1` (arXiv:2611.04934, (P2), p.58). -/
noncomputable def βb (k : ℕ) : ℝ := βδ k / 12

/-- `m_δ := M/2` with `M := M_k`, at the step `k → k+1` (arXiv:2611.04934, (P1), p.58). -/
noncomputable def mδ (k : ℕ) : ℝ := Mseq k / 2

/-- `m_∗ := m_δ + 64M` at the step `k → k+1` (arXiv:2611.04934, (P1), p.58). -/
noncomputable def mstar (k : ℕ) : ℝ := mδ k + 64 * Mseq k

/-- `∆_b := (415/2) M` at the step `k → k+1` (arXiv:2611.04934, (P4), p.58). -/
noncomputable def Δb (k : ℕ) : ℝ := 415 / 2 * Mseq k

/-- `m_b := m_δ + ∆_b` at the step `k → k+1` (arXiv:2611.04934, (P4), p.58). -/
noncomputable def mb (k : ℕ) : ℝ := mδ k + Δb k

/-- `s := (12/13) ∆_b` at the step `k → k+1` (arXiv:2611.04934, (P4), p.58). -/
noncomputable def sSlope (k : ℕ) : ℝ := 12 / 13 * Δb k

/-- `m̄ := m_δ + s` at the step `k → k+1` (arXiv:2611.04934, (P4), p.58). -/
noncomputable def mbar (k : ℕ) : ℝ := mδ k + sSlope k

/-- `ψ_{k+1} := (12/13) ∆_b²/β_δ` at the step `k → k+1` (arXiv:2611.04934, (P4), p.58). -/
noncomputable def ψ (k : ℕ) : ℝ := 12 / 13 * Δb k ^ 2 / βδ k

/-- The rewards of the comb gadget (arXiv:2611.04934, Proposition C.10, p.56, and Definition C.11,
p.57): `m = (5, 12, 4)` on `C₀, C₁, C₂`; at step `j ≥ 1` the dummies get `m^{(j)}_δ = m_δ` of the
step `j−1 → j` and `b_j` gets `M_j`. -/
noncomputable def mU : CombU → ℝ
  | Sum.inl i => ![5, 12, 4] i
  | Sum.inr (j, i) => if i = 2 then Mseq j else mδ (j - 1)

/-- The curvatures of the comb gadget (arXiv:2611.04934, Proposition C.10, p.56, and
Definition C.11, p.57): `β = (1, 4, 4)` on `C₀, C₁, C₂`; at step `j ≥ 1` the dummies get
`β^{(j)}_δ = β_δ` of the step `j−1 → j` and `b_j` gets `β^{(j)}_δ/12`. -/
noncomputable def βU : CombU → ℝ
  | Sum.inl i => ![1, 4, 4] i
  | Sum.inr (j, i) => if i = 2 then βδ (j - 1) / 12 else βδ (j - 1)

/-- The ground set `E_j` of level `j` (arXiv:2611.04934, Definition C.11, p.57): `E₀ = {C₀, C₁, C₂}`
and `E_j := E_{j−1} ∪ {τ_{1,j}, τ_{2,j}, b_j}`. -/
def Elev : ℕ → Finset CombU
  | 0 => Finset.univ.map Function.Embedding.inl
  | k + 1 => Elev k ∪ {tau1 (k + 1), tau2 (k + 1), bnew (k + 1)}

/-- `E := E_k ∪ {τ₁, τ₂}` at the step `k → k+1` (arXiv:2611.04934, Definition C.12, p.58), the
ground set of `f_{k+1}` and `h_{k+1}`. -/
def Eext (k : ℕ) : Finset CombU := Elev k ∪ {tau1 (k + 1), tau2 (k + 1)}

/-- The width `δ := 1/(3µ^in_1)` (arXiv:2611.04934, Definition C.11, p.57).

**Formalization Note** `µ^in` is a list of naturals indexed from `0`, so `µ^in_1` is entry `0`. -/
noncomputable def δw (μin : List ℕ) : ℝ := 1 / (3 * (μin.getD 0 0 : ℝ))

/-- `µ_j := δ µ^in_{j+1}` for `0 ≤ j ≤ k − 1` (arXiv:2611.04934, Definition C.11, p.57), so that
`µ₀ = 1/3`.

**Formalization Note** `µ^in_{j+1}` is entry `j` of the list; beyond the length of `µ^in` the value
is `0` and is never used by the statements, which require the length they need. -/
noncomputable def μs (μin : List ℕ) (j : ℕ) : ℝ := δw μin * (μin.getD j 0 : ℝ)

/-- `ε₀ := 1/30` (arXiv:2611.04934, Proposition C.10, p.56). -/
noncomputable def ε0 : ℝ := 1 / 30

/-- `R₀ := ζ₁ − ε₀ = 3/10` (arXiv:2611.04934, Proposition C.10, p.56). -/
noncomputable def R0 : ℝ := 3 / 10

/-- `ι := 1/100` (arXiv:2611.04934, §C.5.2, p.58). -/
noncomputable def iotaC : ℝ := 1 / 100

/-- `R^{(j)}_1 := ζ₁ + Σ_{i=0}^{j} µ_i + ε₀` with `ζ₁ = 1/3` (arXiv:2611.04934, Definition C.11,
p.57); the window of level `j` is `R_j = [R₀, R^{(j)}_1]`. -/
noncomputable def R1 (μin : List ℕ) (j : ℕ) : ℝ := 1 / 3 + ∑ i ∈ Finset.range (j + 1), μs μin i + ε0

/-- `d_e := µ(m_∗ − m_e)/β_e` at the step `k → k+1`, with `µ := µ_{k+1}` (arXiv:2611.04934,
Definition C.11, p.57, and (P3), p.58); for the dummies this is `w/β_δ`. -/
noncomputable def dvec (μin : List ℕ) (k : ℕ) (e : CombU) : ℝ :=
  μs μin (k + 1) * (mstar k - mU e) / βU e

/-- The numbers of a level fixed by the parameter rule (arXiv:2611.04934, Definition C.12, p.58):
the line `L(α) = p + qα`, the values `F_{τ1}`, `F_{τ2}` of the dummies and the constant `K`. -/
structure LevelParams where
  /-- The intercept `p_k` of the line `L_k`. -/
  p : ℝ
  /-- The slope `q_k` of the line `L_k`. -/
  q : ℝ
  /-- `F^{(k)}_{τ1}`. -/
  Fτ1 : ℝ
  /-- `F^{(k)}_{τ2}`. -/
  Fτ2 : ℝ
  /-- `K_k`. -/
  K : ℝ

namespace LevelParams

/-- `w := 64Mµ` (arXiv:2611.04934, (P3), p.58). -/
noncomputable def w (μin : List ℕ) (k : ℕ) : ℝ := 64 * Mseq k * μs μin (k + 1)

/-- `d(E_k)` (arXiv:2611.04934, (P3), p.58). -/
noncomputable def dEk (μin : List ℕ) (k : ℕ) : ℝ := ∑ e ∈ Elev k, dvec μin k e

/-- `d(E)` with `E = E_k ∪ {τ₁, τ₂}` (arXiv:2611.04934, (P7), p.58). -/
noncomputable def dE (μin : List ℕ) (k : ℕ) : ℝ := ∑ e ∈ Eext k, dvec μin k e

/-- `d̄ := d(E_k)/d_{τ1}` with `d_{τ1} = w/β_δ` (arXiv:2611.04934, (P3), p.58). -/
noncomputable def dbar (μin : List ℕ) (k : ℕ) : ℝ := dEk μin k / (w μin k / βδ k)

/-- `Π := Σ_{e ∈ E_k} (m_δ − m_e) d_e` (arXiv:2611.04934, (P5), p.58). -/
noncomputable def PiSum (μin : List ℕ) (k : ℕ) : ℝ := ∑ e ∈ Elev k, (mδ k - mU e) * dvec μin k e

/-- `∆F := w/β_δ + d(E_k) − (q_k µ − Π)/s` (arXiv:2611.04934, (P5), p.58); `st` is the data of
level `k`. -/
noncomputable def ΔF (μin : List ℕ) (k : ℕ) (st : LevelParams) : ℝ :=
  w μin k / βδ k + dEk μin k - (st.q * μs μin (k + 1) - PiSum μin k) / sSlope k

/-- `ρ̄₀ := 7/6` and `ρ̄_k := R₀ m^{(k)}_δ − β^{(k)}_δ F^{(k)}_{τ2}` for `k ≥ 1` (arXiv:2611.04934,
(P6), p.58); `st` is the data of level `k`. -/
noncomputable def ρbar (k : ℕ) (st : LevelParams) : ℝ :=
  if k = 0 then 7 / 6 else R0 * mδ (k - 1) - βδ (k - 1) * st.Fτ2

/-- `|R| := R₁ − R₀` with `R₁ = R^{(k)}_1` (arXiv:2611.04934, Definition C.12, p.58). -/
noncomputable def absR (μin : List ℕ) (k : ℕ) : ℝ := R1 μin k - R0

/-- `a₂ := (12/13)(µ − |R|/2)` (arXiv:2611.04934, (P6), p.58). -/
noncomputable def a2 (μin : List ℕ) (k : ℕ) : ℝ := 12 / 13 * (μs μin (k + 1) - absR μin k / 2)

/-- `a₀ := β_δ(q_k µ − Π)` (arXiv:2611.04934, (P6), p.58). -/
noncomputable def a0 (μin : List ℕ) (k : ℕ) (st : LevelParams) : ℝ :=
  βδ k * (st.q * μs μin (k + 1) - PiSum μin k)

/-- `u₀ := a₂∆_b − (1/2 + d̄)w + a₀/∆_b` (arXiv:2611.04934, (P6), p.58). -/
noncomputable def u0 (μin : List ℕ) (k : ℕ) (st : LevelParams) : ℝ :=
  a2 μin k * Δb k - (1 / 2 + dbar μin k) * w μin k + a0 μin k st / Δb k

/-- `F_{τ2} := (R₀m_δ − ρ̄_k − w + u₀ − sι)/β_δ` (arXiv:2611.04934, (P6), p.58). -/
noncomputable def Fτ2new (μin : List ℕ) (k : ℕ) (st : LevelParams) : ℝ :=
  (R0 * mδ k - ρbar k st - w μin k + u0 μin k st - sSlope k * iotaC) / βδ k

/-- `F_{τ1} := F_{τ2} + ∆F` (arXiv:2611.04934, (P6), p.58). -/
noncomputable def Fτ1new (μin : List ℕ) (k : ℕ) (st : LevelParams) : ℝ :=
  Fτ2new μin k st + ΔF μin k st

/-- `K := d(E) + 12F_{τ1} − 13(w/2 − s(R₀ + R₁)/2)/β_δ` (arXiv:2611.04934, (P7), p.58). -/
noncomputable def Knew (μin : List ℕ) (k : ℕ) (st : LevelParams) : ℝ :=
  dE μin k + 12 * Fτ1new μin k st - 13 * (w μin k / 2 - sSlope k * (R0 + R1 μin k) / 2) / βδ k

/-- The data of level `k + 1` from those of level `k` (arXiv:2611.04934, Definition C.12, (P6)–(P8),
p.58): `q_{k+1} := q_k + ψ_{k+1}`, `p_{k+1} := p_k + m_δF_{τ2} + (K − d(E) + F_{τ1}) m̄`, and
`F^{(k+1)}_{τ1}`, `F^{(k+1)}_{τ2}`, `K_{k+1}` from (P6), (P7). -/
noncomputable def next (μin : List ℕ) (k : ℕ) (st : LevelParams) : LevelParams where
  p := st.p + mδ k * Fτ2new μin k st + (Knew μin k st - dE μin k + Fτ1new μin k st) * mbar k
  q := st.q + ψ k
  Fτ1 := Fτ1new μin k st
  Fτ2 := Fτ2new μin k st
  K := Knew μin k st

end LevelParams

/-- The **parameter rule** (arXiv:2611.04934, Definition C.12, p.58), by recursion on the level:
level `0` has the line `L₀(α) = 10 + 7α` of Proposition C.10, and level `k + 1` gets the numbers of
`LevelParams.next`. The fields `Fτ1`, `Fτ2`, `K` of level `0` are unused.

**Formalization Note** The rule is trace-free: no best response enters. The rewards `M_k`,
`m_δ` and the curvatures `β_δ`, `β_b` are the explicit functions `Mseq`, `mδ`, `βδ`, `βb` of the
step index, exactly as (P1), (P2), (P4) define them. -/
noncomputable def params (μin : List ℕ) : ℕ → LevelParams
  | 0 => ⟨10, 7, 0, 0, 0⟩
  | k + 1 => LevelParams.next μin k (params μin k)

end PolyContract.Supplement


