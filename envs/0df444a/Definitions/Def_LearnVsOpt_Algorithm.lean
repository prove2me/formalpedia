-- Prove2me | Definitions.Def_LearnVsOpt_Algorithm
-- name    : LearnVsOpt_Algorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:05:59.167489+00:00
-- url     : https://prove2.me/theorems/ab64853a-9a47-47b7-980f-468755868099
-- title:
--   Algorithms 1 and 2 as a charged program: the learner's state, move and update
-- statement:
--   The learner as a program. Its inputs are the horizon $T$, its budget rate $\rho_L$, its null action $j_0$ and its tie-breaking rule; it does not see the matrices, $n_O$ or $i_t$. Its state holds the completed rounds, the historical spending, the observed dictionary $\mathcal{UC}_t$ in order of first observation (with $\mathcal{UC}_0=\{0\}$), and $Z_t$.
--
--   **Algorithm 2.** Set $M_t=50\,\hat n_{t-1}T^2$ and $\eta_t=2/M_t$, and start from the uniform forecast. For $m=1,\dots,M_t$, compute the response at $f^{(m)}$, the drift vector $z_k(f^{(m)})=\langle Z_{t-1},\delta(f^{(m)},k)\rangle$, and $f^{(m+1)}=\Pi_\Delta\big(f^{(m)}+\eta_t z(f^{(m)})\big)$. The forecast law $F_t$ is uniform on the $M_t$ iterates, with multiplicity.
--
--   **Algorithm 1, the move.** In round $t$, if the historical spending exceeds $t\rho_L-1$, the round is non-active and the learner plays $j_0$. Otherwise it obtains $F_t$, draws $f^{(t)}\sim F_t$, and plays $j_t\sim y(f^{(t)})$.
--
--   **The update.** The learner observes $(U_L[i_t,:],C_L[i_t,:])$, adds the realized cost to its spending, and adds the vector to the dictionary if it is new. In an active round, $Z_t=Z_{t-1}+\mathbb E_{f\sim F_t}[\delta(f,k_t)]$.
--
--   **Formalization Note** Every step is charged. $R_t$ is stored as a list of atoms $(k,j_1,j_2,w,q)$ evaluated through (6), and $2\sqrt{n_L}L_t$ is stored in place of $L_t$, so the program uses no square root. The projection is a scan: with $\theta=\max_i\big(\sum_{l:z_l\ge z_i}z_l-1\big)/|\{l:z_l\ge z_i\}|$, it returns $\max\{z_l-\theta,0\}$. The dictionary is updated in every round, and $Z$ only in active rounds.
-- source:
--   Fikioris, Sivan & Tardos, Learning vs. Optimizing Players in Budgeted Games, arXiv:2611.05580, Algorithm 1, p.7; (3)–(4), p.8; (6), p.9; (10), p.12; (13), p.15; p.16; Algorithm 2, p.17; Lemma 6.2, p.17

import Mathlib
import Definitions.Def_LearnVsOpt_Errors

open scoped Matrix

namespace LearnVsOpt

variable {nL : ℕ}

/-- One term `w 1_{·≤q}` of the coordinate `(k, j₁, j₂)` of `R_t`. -/
structure Atom (nL : ℕ) where
  /-- The index `k` of the dictionary entry. -/
  k : ℕ
  /-- The action `j₁`. -/
  j₁ : Fin nL
  /-- The action `j₂`. -/
  j₂ : Fin nL
  /-- The weight. -/
  w : ℝ
  /-- The threshold. -/
  q : ℝ

/-- One iterate `f^(m)` of Algorithm 2 with the response `J⃗(f^(m)), Q(f^(m)), λ(f^(m))`. -/
structure Iterate (nL : ℕ) where
  /-- The forecast, an array over the dictionary. -/
  f : List ℝ
  /-- The selector's response at `uc(f)`. -/
  s : Selection nL

/-- The iterate as a forecast `ℕ → ℝ`, zero past the dictionary. -/
def Iterate.fn (it : Iterate nL) : ℕ → ℝ := fun k => it.f.getD k 0

/-- **The learner's state** between rounds: the number of completed rounds, the historical spending,
the observed dictionary `𝒰𝒞_t` (in order of first observation, `uc^(1) = 0` first), the atoms of `R_t`,
and `2√n_L · L_t`.

**Formalization Note.** Storing `2√n_L · L_t` keeps the program free of square roots, since
`⟨L, δ^L⟩ = ⟨2√n_L L, 2√n_L δ^L⟩/(4n_L)`. `LState.Z` reads `Z_t` off the state, so the `Z_t` of the
theorems is the program's own. -/
structure LState (nL : ℕ) where
  /-- The number of completed rounds. -/
  round : ℕ
  /-- The historical spending. -/
  spent : ℝ
  /-- The observed dictionary. -/
  dict : List (UC nL)
  /-- The atoms of `R_t`. -/
  atoms : List (Atom nL)
  /-- `2√n_L L^u_t`. -/
  Lu : Fin nL → ℝ
  /-- `2√n_L L^c_t`. -/
  Lc : Fin nL → ℝ
  /-- `2√n_L L^{uy}_t`. -/
  Luy : ℝ
  /-- `2√n_L L^{cy}_t`. -/
  Lcy : ℝ

/-- The state before round `1`: `𝒰𝒞_0 = {0}` (p.16), zero spending, `Z_0 = 0`. -/
def LState.init (nL : ℕ) : LState nL := ⟨0, 0, [0], [], 0, 0, 0, 0⟩

/-- `Z_t = (R_t, L_t)` read off the state: `R_{k,j₁,j₂}(q) = Σ_a w_a 1_{q≤q_a}` over the atoms `a` of
coordinate `(k, j₁, j₂)`, and `L_t = (2√n_L L_t)/(2√n_L)`. -/
noncomputable def LState.Z (st : LState nL) : JointVec nL where
  R := fun k j₁ j₂ q => open Classical in
    (st.atoms.map fun a => if a.k = k ∧ a.j₁ = j₁ ∧ a.j₂ = j₂ ∧ q ≤ a.q then a.w else 0).sum
  Lu := fun j => st.Lu j / (2 * Real.sqrt nL)
  Lc := fun j => st.Lc j / (2 * Real.sqrt nL)
  Luy := st.Luy / (2 * Real.sqrt nL)
  Lcy := st.Lcy / (2 * Real.sqrt nL)

/-- The learner's inputs: the horizon, its budget rate, its null action and its tie-breaking rule.
This is everything the learner knows in advance: not the matrices, not `n_O`, not `i_t` (p.2, "It
observes neither `i_t` nor the optimizer's payoffs"). -/
structure Params (nL : ℕ) where
  /-- The horizon `T`. -/
  T : ℕ
  /-- The budget rate `ρ_L`. -/
  ρL : ℝ
  /-- The null action. -/
  j₀ : Fin nL
  /-- The tie-breaking rule. -/
  sel : Selector nL

/-- `uc(f)` computed in a charged loop. -/
noncomputable def ucD (D : List (UC nL)) (f : List ℝ) : Det (UC nL) := do
  let u ← tabD fun j => sumD (List.range D.length) fun k => opn 3 (f.getD k 0 * (D.getD k 0).1 j)
  let c ← tabD fun j => sumD (List.range D.length) fun k => opn 3 (f.getD k 0 * (D.getD k 0).2 j)
  pure (u, c)

/-- `Σ_a w_a (1 + min{q_a, Q})` over the atoms of the coordinate `(k', J⃗)`: the inner product (6) of
this coordinate with the step function `1_{·≤Q}`. -/
noncomputable def rCoord (A : List (Atom nL)) (s : Selection nL) (k' : ℕ) : Det ℝ :=
  sumD A fun a =>
    opn 6 (if a.k = k' ∧ a.j₁ = s.j₁ ∧ a.j₂ = s.j₂ then a.w * (1 + min a.q s.Q) else 0)

/-- **The drift vector** `z_k(f) = ⟨Z_{t−1}, δ(f, k)⟩`, `k ∈ [n̂_{t−1}]` (Algorithm 2, p.17), by (6):
the `R`-part is `Σ_{k'} (1_{k=k'} − f_{k'}) ⟨R_{k',J⃗(f)}, 1_{·≤Q(f)}⟩`. -/
noncomputable def driftVec (P : Params nL) (st : LState nL) (uf : UC nL) (it : Iterate nL) :
    Det (List ℝ) := do
  let n := st.dict.length
  let rs ← mapD (List.range n) (rCoord st.atoms it.s)
  let fr ← sumD (List.range n) fun k' => opn 3 (it.f.getD k' 0 * rs.getD k' 0)
  mapD (List.range n) fun k => do
    let e ← opn 1 (st.dict.getD k 0)
    let lu ← sumD (List.finRange nL) fun j => opn 4 (st.Lu j * (e.1 j - uf.1 j))
    let lc ← sumD (List.finRange nL) fun j => opn 6 (st.Lc j * (P.ρL * it.s.lam * (e.2 j - uf.2 j)))
    let duy ← opn 8 (it.s.Q * (e.1 it.s.j₁ - uf.1 it.s.j₁) + (1 - it.s.Q) * (e.1 it.s.j₂ - uf.1 it.s.j₂))
    let dcy ← opn 8 (it.s.Q * (e.2 it.s.j₁ - uf.2 it.s.j₁) + (1 - it.s.Q) * (e.2 it.s.j₂ - uf.2 it.s.j₂))
    opn 9 (rs.getD k 0 - fr + (lu + lc + st.Luy * duy + st.Lcy * dcy) / (4 * (nL : ℝ)))

open Classical in
/-- The Euclidean projection `Π_Δ(z)` onto the simplex (Algorithm 2, p.17) by a scan: with
`θ = max_i (Σ_{l : z_l ≥ z_i} z_l − 1) / |{l : z_l ≥ z_i}|`, the projection is `max{z_l − θ, 0}`. That
this is the Euclidean projection is a proof obligation of Lemma 6.1. -/
noncomputable def proj (z : List ℝ) : Det (List ℝ) := do
  let thetas ← mapD z fun zi => do
    let s ← sumD z fun zl => opn 2 (if zi ≤ zl then zl else 0)
    let c ← sumD z fun zl => opn 2 (if zi ≤ zl then 1 else 0)
    opn 2 ((s - 1) / c)
  let θ ← foldD thetas (fun b a => opn 1 (max b a)) (thetas.getD 0 0)
  mapD z fun zl => opn 2 (max (zl - θ) 0)

/-- **Algorithm 2** (Projected Gradient Ascent Forecaster, p.17): with `M_t = 50 n̂_{t−1} T²` and
`η_t = 2/M_t`, starting from the uniform forecast, for `m = 1, …, M_t` compute the response at
`f^(m)`, the drift vector `z(f^(m))`, and `f^(m+1) = Π_Δ(f^(m) + η_t z(f^(m)))`. The output is the list
of the `M_t` iterates: `F_t` is the uniform law on this list (with multiplicity, p.17, `E_{f∼F_t}[…] =
(1/M_t) Σ_m …`). -/
noncomputable def forecast (P : Params nL) (st : LState nL) : Det (List (Iterate nL)) := do
  let n : ℕ ← opn 1 st.dict.length
  let M : ℕ ← opn 3 (50 * n * P.T ^ 2)
  let η ← opn 2 (2 / (M : ℝ))
  let f₁ ← mapD (List.range n) fun _ => opn 2 (1 / (n : ℝ))
  let r ← foldD (List.range M) (fun (acc : List (Iterate nL) × List ℝ) _ => do
    let f := acc.2
    let uf ← ucD st.dict f
    let s ← P.sel uf.1 uf.2
    let it : Iterate nL := ⟨f, s⟩
    let z ← driftVec P st uf it
    let g ← mapD (List.range n) fun k => opn 4 (f.getD k 0 + η * z.getD k 0)
    let f' ← proj g
    opn 1 (acc.1 ++ [it], f')) ([], f₁)
  pure r.1

/-- What the learner does in a round: whether the round is active, the iterates representing `F_t`
(empty in a non-active round), the realized index `m` and the action `j_t`. -/
structure Action (nL : ℕ) where
  /-- Whether the round is active. -/
  active : Bool
  /-- `F_t`. -/
  iters : List (Iterate nL)
  /-- The realized index of `f^(t)` among the iterates (`0` in a non-active round). -/
  m : ℕ
  /-- The action `j_t`. -/
  j : Fin nL

open Classical in
/-- **Algorithm 1, the learner's move in round `t = st.round + 1`** (p.7). If the historical spending
exceeds `tρ_L − 1`, the round is non-active and the learner plays the null action. Otherwise it receives
`F_t` from Algorithm 2, draws `f^(t) ∼ F_t`, and plays `j_t ∼ y(f^(t))`.

**Formalization Note.** The move depends on the state only, so `j_t` depends on the past and not on
`i_t`. -/
noncomputable def act (P : Params nL) (st : LState nL) : Prog (Action nL) := do
  charge 3
  if st.spent > ((st.round + 1 : ℕ) : ℝ) * P.ρL - 1 then
    pure ⟨false, [], 0, P.j₀⟩
  else do
    let iters ← (forecast P st).lift
    charge 1
    let m ← drawRange iters.length
    charge 1
    match iters[m]? with
    | some it =>
      let j ← drawTwo it.s.Q it.s.j₁ it.s.j₂
      pure ⟨true, iters, m, j⟩
    | none => pure ⟨true, iters, m, P.j₀⟩

open Classical in
/-- **The learner's update after round `t`**, on observing the realized vector
`v = (U_L[i_t, :], C_L[i_t, :])` (p.7, full-information feedback): the spending grows by `v.2[j_t]`;
`v` joins the dictionary if new; and in an active round, `Z_t = Z_{t−1} + E_{f∼F_t}[δ(f, k_t)]`.

**Formalization Note.** The dictionary is updated in **every** round, active or not (§2, p.6; p.16,
"observed in rounds `1, …, t`"; proof of Claim 6.6, p.21), and `Z` only in active rounds (proof of
Lemma 6.2, p.17). Algorithm 1's pseudocode indents the observation under the active branch. -/
noncomputable def observe (P : Params nL) (st : LState nL) (a : Action nL) (v : UC nL) :
    Det (LState nL) := do
  let sp ← opn 2 (st.spent + v.2 a.j)
  let idx ← foldD (List.range st.dict.length) (fun (b : Option ℕ) k => do
    let e ← opn 1 (st.dict.getD k 0)
    let same ← foldD (List.finRange nL) (fun (b : Bool) j =>
      opn 3 (b && decide (e.1 j = v.1 j) && decide (e.2 j = v.2 j))) true
    opn 1 (if same then some k else b)) none
  let kt ← opn 1 (idx.getD st.dict.length)
  let D' ← opn 1 (if idx.isSome then st.dict else st.dict ++ [v])
  let base : LState nL := { st with round := st.round + 1, spent := sp, dict := D' }
  if a.active then do
    let M ← opn 1 ((a.iters.length : ℕ) : ℝ)
    foldD a.iters (fun (acc : LState nL) it => do
      let uf ← ucD D' it.f
      let w ← mapD (List.range D'.length) fun k =>
        opn 4 (⟨k, it.s.j₁, it.s.j₂, ((if k = kt then 1 else 0) - it.f.getD k 0) / M, it.s.Q⟩ : Atom nL)
      let lu ← tabD fun j => opn 4 (acc.Lu j + (v.1 j - uf.1 j) / M)
      let lc ← tabD fun j => opn 6 (acc.Lc j + P.ρL * it.s.lam * (v.2 j - uf.2 j) / M)
      let duy ← opn 8 (it.s.Q * (v.1 it.s.j₁ - uf.1 it.s.j₁) + (1 - it.s.Q) * (v.1 it.s.j₂ - uf.1 it.s.j₂))
      let dcy ← opn 8 (it.s.Q * (v.2 it.s.j₁ - uf.2 it.s.j₁) + (1 - it.s.Q) * (v.2 it.s.j₂ - uf.2 it.s.j₂))
      opn 6 { acc with
        atoms := acc.atoms ++ w
        Lu := lu
        Lc := lc
        Luy := acc.Luy + duy / M
        Lcy := acc.Lcy + dcy / M }) base
  else pure base

end LearnVsOpt


