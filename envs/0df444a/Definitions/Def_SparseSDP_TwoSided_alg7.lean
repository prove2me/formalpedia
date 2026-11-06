-- Prove2me | Definitions.Def_SparseSDP_TwoSided_alg7
-- name    : SparseSDP_TwoSided_alg7
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:56:29.689611+00:00
-- url     : https://prove2.me/theorems/c4275e85-888c-4d0a-aca4-41173bb181fc
-- title:
--   Algorithm 7: the two-sided stochastic solver, as a charged program
-- statement:
--   **Algorithm 7** (p. 46), for $k$ real symmetric matrices of size $d$ (the paper's $m$ and $n$) read through a row access, with parameters $\omega,R,r,T,\delta$.
--
--   Lines 1–5 set $\Lambda=\log(16kd/\delta)$, $\delta_L=\delta/3$, $\Lambda_L=\log(4T^2\sqrt d/\delta_L)$, $\eta_X=(r\omega)^{-1}\sqrt{2\log(4d)/(3T)}$, $B=c_BR\omega\sqrt{T/\Lambda}$ and $\eta_y=c_y\min\{1/B,\sqrt{\log(2k)/(R^2\omega^2T)}\}$.
--
--   Round $t=1,\dots,T$:
--
--   1. $\hat p_t=\mathrm{softmax}(-\eta_y\hat\ell_t)$, draw $J_t\sim\hat p_t$ (line 8);
--   2. draw $u_t\sim\mathrm{Unif}(S^{d-1})$ (line 10), set $k_t=\min\{d,\lceil C_L\sqrt{\Lambda_L\max\{\eta_Xr\omega t,\Lambda_L\}}\rceil\}$ (line 11);
--   3. $\tilde v_t=\text{LánczosExp}(\eta_XH_t/2,u_t,k_t)$ and $\tilde\psi_t=\tilde v_t/\|\tilde v_t\|_2$ (lines 12–13);
--   4. draw $I_t$ with $P[I_t=i]=|[\tilde\psi_t]_i|^2$ (line 14);
--   5. $[\hat c_t]_j=\mathrm{clip}_B(RZ_{A_j}(\tilde\psi_t,I_t))$ for all $j$, each from one row scan (lines 15–16);
--   6. $H_{t+1}=H_t+rA_{J_t}$, $\hat\ell_{t+1}=\hat\ell_t+\hat c_t$ (line 17).
--
--   The product with $H_t$ follows Eq. (352): the at most $\min\{t-1,k\}$ distinct sampled matrices are applied row by row until the first round with $\min\{t-1,k\}\ge d/s$; then the dense matrix is formed once, each product costs $d^2$ and each update $O(ds)$. The program returns the trace of the rounds and the final representation of $H_{T+1}$.
--
--   `Consts` gathers the constants the paper leaves as $\Theta(\cdot)$ or "sufficiently large": $C_L$, $c_B$, $c_y\le1$ (so $\eta_yB\le1$), $C_T$ and the certificate constant $c_E$. `polyL` is the polylogarithmic unit $L=\log(2+d+k+\gamma+1/\delta)$ of $\tilde O$.
--
--   **Formalization Note** The matrix $H_t$ never appears as a stored object in sparse mode; it is read off the trace by the pure functions of `Trajectory`.
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Algorithm 7, p. 46; Eqs. (351), (352), p. 62

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_lanczosProg
import Definitions.Def_SparseSDP_TwoSided_sphereLaw
import Definitions.Def_SparseSDP_TwoSided_zHat

open Matrix

namespace SparseSDP.TwoSided

/-- The constants that the paper leaves as `Θ(·)` or "sufficiently large": `C_L` of line 11 of
Algorithm 7, `B = c_B Rω√(T/Λ)`, `η_y = c_y min{…}` with `c_y ≤ 1` so that `η_y B ≤ 1`, the round
constant `C_T` of `T = ⌈C_T γ²Λ⌉` and the constant `c_E` of the Lánczos certificate. -/
structure Consts where
  /-- `C_L`, Algorithm 7, line 11. -/
  CL : ℝ
  /-- The constant of `B`, Algorithm 7, line 4. -/
  cB : ℝ
  /-- The constant of `η_y`, Algorithm 7, line 5. -/
  cy : ℝ
  /-- The constant of the round count. -/
  CT : ℝ
  /-- The constant of the certificate's iteration count. -/
  cE : ℝ
  CL_pos : 0 < CL
  cB_pos : 0 < cB
  cy_pos : 0 < cy
  cy_le : cy ≤ 1
  CT_pos : 0 < CT
  cE_pos : 0 < cE

/-- `Λ = log(16 m n/δ)`, Algorithm 7, line 1, for `k` constraints in dimension `d`. -/
noncomputable def lamP (k d : ℕ) (δ : ℝ) : ℝ := Real.log (16 * k * d / δ)

/-- `Λ_L = log(4T²√n/δ_L)` with `δ_L = δ/3`, Algorithm 7, lines 1–2. -/
noncomputable def lamL (d T : ℕ) (δ : ℝ) : ℝ := Real.log (4 * (T : ℝ) ^ 2 * √(d : ℝ) / (δ / 3))

/-- `η_X = (1/(rω)) √(2 log(4n)/(3T))`, Algorithm 7, line 3. -/
noncomputable def etaX (d T : ℕ) (r ω : ℝ) : ℝ :=
  1 / (r * ω) * √(2 * Real.log (4 * d) / (3 * T))

/-- `B = c_B Rω√(T/Λ)`, Algorithm 7, line 4. -/
noncomputable def clipLevel (P : Consts) (k d T : ℕ) (R ω δ : ℝ) : ℝ :=
  P.cB * (R * ω) * √((T : ℝ) / lamP k d δ)

/-- `η_y = c_y min{1/B, √(log(2m)/(R²ω²T))}`, Algorithm 7, line 5. -/
noncomputable def etaY (P : Consts) (k d T : ℕ) (R ω δ : ℝ) : ℝ :=
  P.cy * min (1 / clipLevel P k d T R ω δ)
    (√(Real.log (2 * k) / (R ^ 2 * ω ^ 2 * T)))

/-- `k_t = min{n, ⌈C_L √(Λ_L max{η_X rω t, Λ_L})⌉}`, Algorithm 7, line 11. -/
noncomputable def kRound (P : Consts) (d T : ℕ) (r ω δ : ℝ) (t : ℕ) : ℕ :=
  min d ⌈P.CL * √(lamL d T δ * max (etaX d T r ω * r * ω * t) (lamL d T δ))⌉₊

/-- The polylogarithmic unit of `Õ`: `L = log(2 + n + m + γ + 1/δ)`. -/
noncomputable def polyL (n m : ℕ) (γ δ : ℝ) : ℝ := Real.log (2 + n + m + γ + 1 / δ)

variable {d k : ℕ}

/-- The representation of the accumulated Hamiltonian (p. 62): sample counts, the list of distinct
sampled constraints, and, past the crossover, the dense matrix. -/
structure HRep (d k : ℕ) where
  /-- How often each constraint was sampled. -/
  cnt : Fin k → ℕ
  /-- The distinct sampled constraints. -/
  S : List (Fin k)
  /-- The dense matrix, once formed. -/
  dense : Option (Mat d)

/-- One product with the accumulated Hamiltonian `a ∑ⱼ cntⱼ Mⱼ` (Eq. (352), p. 62): in sparse form
each distinct sampled matrix is applied row by row, in dense form the product costs `d²`.

**Formalization Note.** The dense matrix already contains the factor `a`. -/
noncomputable def applyH (acc : RowAccess d k) (a : ℝ) (rep : HRep d k) (v : Vec d) :
    Prog (Vec d) :=
  match rep.dense with
  | some Hd => op (d * d) (Hd *ᵥ v)
  | none => do
    let mut out : Vec d := 0
    for i in List.finRange d do
      tick 1
      let mut x : ℝ := 0
      for j in rep.S do
        tick 1
        let row ← acc.read j i
        let y ← rowDot row v
        x ← op 3 (x + a * rep.cnt j * y)
      out ← op 1 (Function.update out i x)
    pure out

/-- Add `a` times a sparse row to row `i` of a dense matrix. -/
noncomputable def addRowTo (Hd : Mat d) (i : Fin d) (a : ℝ) (row : SparseRow d) : Prog (Mat d) :=
  op (2 * row.length + 1) fun x y =>
    if x = i then Hd x y + a * ((row.filter fun p => p.1 = y).map Prod.snd).sum else Hd x y

/-- Add `a Mⱼ` to a dense matrix, one row at a time ("Later updates cost `O(ns)` each", p. 62). -/
noncomputable def addGain (acc : RowAccess d k) (a : ℝ) (j : Fin k) (Hd : Mat d) :
    Prog (Mat d) := do
  let mut H := Hd
  for i in List.finRange d do
    tick 1
    let row ← acc.read j i
    H ← addRowTo H i a row
  pure H

/-- Form the dense `a ∑ⱼ cntⱼ Mⱼ` from the distinct sampled matrices (p. 62). -/
noncomputable def densify (acc : RowAccess d k) (a : ℝ) (rep : HRep d k) : Prog (Mat d) := do
  let mut H : Mat d ← op (d * d) 0
  for j in rep.S do
    tick 1
    let w ← op 1 (a * rep.cnt j)
    H ← addGain acc w j H
  pure H

/-- `H_{t+1} ← H_t + G_t` with `G_t = a M_J` (line 17): update the counts and, past the crossover,
the dense matrix. -/
noncomputable def pushGain (acc : RowAccess d k) (a : ℝ) (rep : HRep d k) (J : Fin k) :
    Prog (HRep d k) := do
  tick 3
  let S' := if rep.cnt J = 0 then J :: rep.S else rep.S
  let cnt' := Function.update rep.cnt J (rep.cnt J + 1)
  match rep.dense with
  | some Hd => do
    let Hd' ← addGain acc a J Hd
    pure ⟨cnt', S', some Hd'⟩
  | none => pure ⟨cnt', S', none⟩

/-- The record of one round `t` of Algorithm 7. -/
structure Round (d k : ℕ) where
  /-- `p̂_t`, line 8. -/
  p : Vec k
  /-- `J_t`, line 8. -/
  J : Fin k
  /-- `u_t`, line 10. -/
  u : Vec d
  /-- `k_t`, line 11. -/
  kt : ℕ
  /-- `ψ̃_t`, line 13. -/
  ψ : Vec d
  /-- `I_t`, line 14. -/
  I : Fin d
  /-- `ĉ_t`, line 16. -/
  c : Vec k

/-- The output of Algorithm 7: the trace of the rounds, from which `X^out` and `z^out` are read, and
the final representation of `H_{T+1}`. -/
structure Alg7Out (d k : ℕ) where
  /-- Rounds `1, …, T`, in order. -/
  rounds : List (Round d k)
  /-- The final Hamiltonian. -/
  rep : HRep d k

/-- **Algorithm 7** (Two-Sided Stochastic SDP Solver, p. 46), lines 1–17, with `k` constraints
in dimension `d` (the paper's `m` and `n`), matrices read through `acc`, row sparsity `s`.

The product with `H_t` is that of Eq. (352), p. 62: sparse form until the first round with
`min{t−1, k} ≥ d/s`, then the dense matrix is formed once. -/
noncomputable def alg7 [NeZero d] [NeZero k] (P : Consts) (acc : RowAccess d k) (s : ℕ)
    (ω R r : ℝ) (T : ℕ) (δ : ℝ) : Prog (Alg7Out d k) := do
  let ηX ← op 8 (etaX d T r ω)
  let B ← op 12 (clipLevel P k d T R ω δ)
  let ηy ← op 12 (etaY P k d T R ω δ)
  let mut ell : Vec k := 0
  let mut rep : HRep d k := ⟨0, [], none⟩
  let mut rounds : List (Round d k) := []
  for idx in List.range T do
    tick 1
    let t := idx + 1
    tick 3
    if rep.dense.isNone ∧ d ≤ s * min (t - 1) k then
      let Hd ← densify acc r rep
      rep := { rep with dense := some Hd }
    -- line 8
    let a ← scale (-ηy) ell
    let p ← softmaxP a
    let J ← sampleCat p
    -- line 10
    let u ← drawSphere d
    -- line 11
    let kt ← op 20 (kRound P d T r ω δ t)
    -- line 12
    let v ← lanczosProg
      (fun w => do
        let h ← applyH acc r rep w
        scale (ηX / 2) h) u kt
    -- line 13
    let nv ← nrm v
    let inv ← op 1 (1 / nv)
    let ψ ← scale inv v
    -- line 14
    let I ← sampleCoord ψ
    -- lines 15–16
    let mut c : Vec k := 0
    for j in List.finRange k do
      tick 1
      let row ← acc.read j I
      let y ← rowDot row ψ
      let z ← op 2 (R * (y / ψ I))
      let cj ← op 3 (clip B z)
      c ← op 1 (Function.update c j cj)
    -- line 17
    ell ← axpy 1 c ell
    rep ← pushGain acc r rep J
    tick 1
    rounds := rounds ++ [⟨p, J, u, kt, ψ, I, c⟩]
  pure ⟨rounds, rep⟩

end SparseSDP.TwoSided


