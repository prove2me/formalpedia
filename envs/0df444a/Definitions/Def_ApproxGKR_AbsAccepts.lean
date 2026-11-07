-- Prove2me | Definitions.Def_ApproxGKR_AbsAccepts
-- name    : ApproxGKR_AbsAccepts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:46.294937+00:00
-- url     : https://prove2.me/theorems/20960f10-c957-4e88-b0e8-0cbf144ebe6e
-- title:
--   The abstract approximate GKR protocol: provers, verifier implementations and acceptance
-- statement:
--   This module states steps 1–3 of the protocol of §C.1 with exact complex messages. A **coin tuple** assigns to each layer $i<L$ the sum-check challenges $r_1,\dots,r_{k_i}$ and the combination coefficient $\lambda_i$, all in $\Omega_N$ (by index). From the coins come the challenge vector $(g_i,u_i,v_i)$, the claim points $(\rho_{i,0},\rho_{i,1})$ (empty at layer $0$, $(u_{i-1},v_{i-1})$ later), the coefficients $(1,0)$ at layer $0$ and $(1,\lambda_{i-1})$ later, the exact claim
--   $$T_i=\widetilde V_i(\rho_{i,0})+c_{i,1}\widetilde V_i(\rho_{i,1}),$$
--   the polynomial $F_i$ of (C.6), the true round polynomials $q_j(X)=\sum_{a\in H^{k_i-j}}F_i(r_1,\dots,r_{j-1},X,a)$, and $w^+_i=\Psi_i(g_i)\widetilde{\mathrm{add}}_i(g_i,u_i,v_i)$, $w^\times_i=\Psi_i(g_i)\widetilde{\mathrm{mult}}_i(g_i,u_i,v_i)$.
--
--   A **prover** gives round polynomials $p_j$ and claimed evaluations $(a_i,b_i)$ as functions of the coins; it is *adapted* if $p_j$ depends only on the earlier coins and $(a_i,b_i)$ does not depend on $\lambda_i$. A **verifier implementation** gives the computed residuals, next claims $Y_j$, gate residuals, combined claims $\widehat T_{i+1}$ and the final residual; it is *within $\Delta_0$* if each is within $\Delta_0$ of the exact quantity ("Each verifier evaluation, linear combination, and residual computation has absolute error at most $\Delta_0$", p.32).
--
--   The run **accepts** if $|y|\le B_V+1$; at every layer every $p_j$ has degree at most $D$, coefficients of modulus at most $C^*$ and computed residual of modulus at most $6\Delta_0$; $|a_i|,|b_i|\le U$; the gate residual has modulus at most $(K+3)\Delta_0$; and the final input residual has modulus at most $4\Delta_0$.
--
--   **Formalization Note** The verifier's computed values are arbitrary functions of the coin tuple, which covers every implementation (and every rounding rule). The oracle's error is part of the gate residual's $\Delta_0$ allowance, as on p.32.
-- source:
--   Das, Gupta, Mondal, More, Delegating Computation with Approximate Arithmetic: Interactive Proofs for Wizards (manuscript, sha256 78b2a36b…), §C.1, pp.31–33

import Mathlib
import Definitions.Def_ApproxGKR_LayeredCircuit
import Definitions.Def_ApproxGKR_constK

namespace ApproxGKR

/-! The abstract approximate GKR protocol of §C.1, steps 1–3 (pp.32–33), with exact complex
messages and with every verifier computation given as an arbitrary function of the coins (hence
of the transcript), constrained to lie within `∆₀` of the exact quantity. -/

variable (C : LayeredCircuit) (N : ℕ)

/-- A coin tuple: for each layer `i < L` and position `j ≤ kᵢ` an index in `Fin N` standing for a
root of `Ω_N`; positions `j < kᵢ` are the sum-check challenges `r_{j+1}`, position `kᵢ` is `λᵢ`. -/
abbrev Coins : Type := (i : Fin C.L) → Fin (C.ki i + 1) → Fin N

variable {C N}

/-- The coin index at layer `i`, position `j` (`0` outside the range). -/
def coinAt (c : Coins C N) (i j : ℕ) : ℕ :=
  if hi : i < C.L then
    if hj : j < C.ki i + 1 then (c ⟨i, hi⟩ ⟨j, hj⟩ : ℕ) else 0
  else 0

/-- The challenge vector `(gᵢ, uᵢ, vᵢ) ∈ Ω_N^{kᵢ}` of layer `i`. -/
noncomputable def chal (c : Coins C N) (i : ℕ) : Fin (C.ki i) → ℂ :=
  fun v => root N (coinAt c i v)

/-- The part `gᵢ ∈ Ω_N^{mᵢ}` of the challenge vector. -/
noncomputable def gPt (c : Coins C N) (i : ℕ) : Fin (C.m i) → ℂ :=
  fun j => root N (coinAt c i j)

/-- The part `uᵢ ∈ Ω_N^{mᵢ₊₁}` of the challenge vector. -/
noncomputable def uPt (c : Coins C N) (i : ℕ) : Fin (C.m (i + 1)) → ℂ :=
  fun j => root N (coinAt c i (C.m i + j))

/-- The part `vᵢ ∈ Ω_N^{mᵢ₊₁}` of the challenge vector. -/
noncomputable def vPt (c : Coins C N) (i : ℕ) : Fin (C.m (i + 1)) → ℂ :=
  fun j => root N (coinAt c i (C.m i + C.m (i + 1) + j))

/-- The combination coefficient `λᵢ ∈ Ω_N`. -/
noncomputable def lam (c : Coins C N) (i : ℕ) : ℂ := root N (coinAt c i (C.ki i))

/-- The first claim point `ρ_{i,0}`: empty at layer 0, `u_{i−1}` later (step 3, p.33). -/
noncomputable def rho0 (c : Coins C N) : (i : ℕ) → Fin (C.m i) → ℂ
  | 0 => fun _ => 0
  | i + 1 => uPt c i

/-- The second claim point `ρ_{i,1}`: empty at layer 0, `v_{i−1}` later. -/
noncomputable def rho1 (c : Coins C N) : (i : ℕ) → Fin (C.m i) → ℂ
  | 0 => fun _ => 0
  | i + 1 => vPt c i

/-- The second claim coefficient `c_{i,1}`: `0` at layer 0, `λ_{i−1}` later; `c_{i,0} = 1`
("`(c₀,₀, c₀,₁) = (1, 0)`", p.31; "`(cᵢ₊₁,₀, cᵢ₊₁,₁) = (1, λᵢ)`", p.33). -/
noncomputable def coef1 (c : Coins C N) : ℕ → ℂ
  | 0 => 0
  | i + 1 => lam c i

/-- The exact claim `Tᵢ = c_{i,0} Ṽᵢ(ρ_{i,0}) + c_{i,1} Ṽᵢ(ρ_{i,1})` (eq. (C.2), p.31). -/
noncomputable def Tclaim (x : InputList) (c : Coins C N) (i : ℕ) : ℂ :=
  MvPolynomial.eval (rho0 c i) (Vt C x i) + coef1 c i * MvPolynomial.eval (rho1 c i) (Vt C x i)

/-- `Ψᵢ` of eq. (C.4) at layer `i` for the claim points and coefficients of the run. -/
noncomputable def PsiAt (c : Coins C N) (i : ℕ) : MvPolynomial (Fin (C.m i)) ℂ :=
  Psi C.h (rho0 c i) (rho1 c i) 1 (coef1 c i)

/-- Embedding of the `g` coordinates into `Fin kᵢ`. -/
def gEmb (C : LayeredCircuit) (i : ℕ) : Fin (C.m i) → Fin (C.ki i) :=
  fun j => ⟨j, by have := j.isLt; simp only [LayeredCircuit.ki]; omega⟩

/-- Embedding of the `u` coordinates into `Fin kᵢ`. -/
def uEmb (C : LayeredCircuit) (i : ℕ) : Fin (C.m (i + 1)) → Fin (C.ki i) :=
  fun j => ⟨C.m i + j, by have := j.isLt; simp only [LayeredCircuit.ki]; omega⟩

/-- Embedding of the `v` coordinates into `Fin kᵢ`. -/
def vEmb (C : LayeredCircuit) (i : ℕ) : Fin (C.m (i + 1)) → Fin (C.ki i) :=
  fun j => ⟨C.m i + C.m (i + 1) + j, by have := j.isLt; simp only [LayeredCircuit.ki]; omega⟩

/-- `Fᵢ(g,u,v) = Ψᵢ(g)[add~ᵢ(g,u,v)(Ṽᵢ₊₁(u) + Ṽᵢ₊₁(v)) + mult~ᵢ(g,u,v)Ṽᵢ₊₁(u)Ṽᵢ₊₁(v)]`
(eq. (C.6), p.31), as a polynomial in the `kᵢ` variables `(g, u, v)`. -/
noncomputable def Fpoly (ext : ExtFamily C) (x : InputList) (c : Coins C N) (i : ℕ) :
    MvPolynomial (Fin (C.ki i)) ℂ :=
  MvPolynomial.rename (gEmb C i) (PsiAt c i) *
    (ext i GateType.add *
        (MvPolynomial.rename (uEmb C i) (Vt C x (i + 1)) +
          MvPolynomial.rename (vEmb C i) (Vt C x (i + 1))) +
      ext i GateType.mult *
        (MvPolynomial.rename (uEmb C i) (Vt C x (i + 1)) *
          MvPolynomial.rename (vEmb C i) (Vt C x (i + 1))))

open Classical in
/-- The true round polynomial `q_j(X) = Σ_{a ∈ H^{kᵢ−j}} Fᵢ(r₁, …, r_{j−1}, X, a)` of round
`j ∈ {1, …, kᵢ}` at layer `i` (p.31): coordinates `< j−1` are the challenges, coordinate `j−1` is
`X`, coordinates `≥ j` are summed over `H` (the filter fixes the unused summation indices). -/
noncomputable def roundPoly (ext : ExtFamily C) (x : InputList) (c : Coins C N) (i j : ℕ) :
    Polynomial ℂ :=
  ∑ a ∈ Finset.univ.filter (fun a : Fin (C.ki i) → Fin C.h => ∀ v : Fin (C.ki i), (v : ℕ) < j → a v = 0),
    MvPolynomial.aeval
      (fun v : Fin (C.ki i) =>
        if (v : ℕ) + 1 < j then Polynomial.C (root N (coinAt c i v))
        else if (v : ℕ) + 1 = j then Polynomial.X
        else Polynomial.C (root C.h (a v).val))
      (Fpoly ext x c i)

/-- `w⁺ᵢ = Ψᵢ(gᵢ) add~ᵢ(gᵢ, uᵢ, vᵢ)` (step 2, p.33), exact. -/
noncomputable def wplus (ext : ExtFamily C) (c : Coins C N) (i : ℕ) : ℂ :=
  MvPolynomial.eval (gPt c i) (PsiAt c i) * MvPolynomial.eval (chal c i) (ext i GateType.add)

/-- `w×ᵢ = Ψᵢ(gᵢ) mult~ᵢ(gᵢ, uᵢ, vᵢ)` (step 2, p.33), exact. -/
noncomputable def wtimes (ext : ExtFamily C) (c : Coins C N) (i : ℕ) : ℂ :=
  MvPolynomial.eval (gPt c i) (PsiAt c i) * MvPolynomial.eval (chal c i) (ext i GateType.mult)

/-- A prover of the abstract protocol: round polynomials `p_j` (layer `i`, round `j ≥ 1`) and
claimed evaluations `(aᵢ, bᵢ)`, as functions of the coin tuple. -/
structure AbsProver (C : LayeredCircuit) (N : ℕ) where
  poly : ℕ → ℕ → Coins C N → Polynomial ℂ
  claims : ℕ → Coins C N → ℂ × ℂ

/-- The prover is adaptive but cannot see future coins: `p_j` at layer `i` depends only on the
coins of earlier layers and on `r₁, …, r_{j−1}`; `(aᵢ, bᵢ)` only on the coins of earlier layers
and on all `r`'s of layer `i`, not on `λᵢ` ("Each polynomial is sent before its challenge is
sampled", p.32; "Only after `aᵢ, bᵢ` are fixed, sample a fresh uniform `λᵢ`", p.33). -/
def AbsProver.Adapted (P : AbsProver C N) : Prop :=
  (∀ (i j : ℕ) (c c' : Coins C N),
    (∀ i' j', i' < i ∨ (i' = i ∧ j' + 1 < j) → coinAt c i' j' = coinAt c' i' j') →
      P.poly i j c = P.poly i j c') ∧
  (∀ (i : ℕ) (c c' : Coins C N),
    (∀ i' j', i' < i ∨ (i' = i ∧ j' < C.ki i) → coinAt c i' j' = coinAt c' i' j') →
      P.claims i c = P.claims i c')

/-- A verifier implementation: the computed values of every quantity the verifier computes.
`res i j` the residual of round `j`, `Y i j` the next claim `Y_j` (`j ≥ 1`), `gres i` the gate
residual, `That (i+1)` the combined claim `T̂ᵢ₊₁`, `fres` the final input residual. -/
structure AbsVerifier (C : LayeredCircuit) (N : ℕ) where
  res : ℕ → ℕ → Coins C N → ℂ
  Y : ℕ → ℕ → Coins C N → ℂ
  gres : ℕ → Coins C N → ℂ
  That : ℕ → Coins C N → ℂ
  fres : Coins C N → ℂ

/-- The current sum-check claim `Y_j` at layer `i`: `Y₀ = T̂ᵢ` (with `T̂₀ = y`), then the
computed `Y_j`. -/
def claimY (V : AbsVerifier C N) (y : ℂ) (c : Coins C N) (i j : ℕ) : ℂ :=
  if j = 0 then (if i = 0 then y else V.That i c) else V.Y i j c

/-- Every verifier computation has absolute error at most `∆₀` ("Each verifier evaluation,
linear combination, and residual computation has absolute error at most `∆0`", p.32; the oracle's
error is part of the gate-check allowance, p.32). The exact quantities are the residual
`Y_{j−1} − Σ_{a∈H} p_j(a)`, `p_j(r_j)`, `Zᵢ − w⁺ᵢ(aᵢ + bᵢ) − w×ᵢ aᵢbᵢ` with `Zᵢ = Y_{kᵢ}`,
`aᵢ + λᵢ bᵢ`, and `T̂_L − T_L`. -/
def AbsVerifier.Within (V : AbsVerifier C N) (P : AbsProver C N) (ext : ExtFamily C)
    (x : InputList) (y : ℂ) (Δ₀ : ℝ) : Prop :=
  (∀ (c : Coins C N) (i j : ℕ), i < C.L → 1 ≤ j → j ≤ C.ki i →
    ‖V.res i j c - (claimY V y c i (j - 1) -
        ∑ a : Fin C.h, (P.poly i j c).eval (root C.h a.val))‖ ≤ Δ₀ ∧
    ‖V.Y i j c - (P.poly i j c).eval (root N (coinAt c i (j - 1)))‖ ≤ Δ₀) ∧
  (∀ (c : Coins C N) (i : ℕ), i < C.L →
    ‖V.gres i c - (claimY V y c i (C.ki i) -
        wplus ext c i * ((P.claims i c).1 + (P.claims i c).2) -
        wtimes ext c i * ((P.claims i c).1 * (P.claims i c).2))‖ ≤ Δ₀ ∧
    ‖V.That (i + 1) c - ((P.claims i c).1 + lam c i * (P.claims i c).2)‖ ≤ Δ₀) ∧
  (∀ c : Coins C N, ‖V.fres c - (V.That C.L c - Tclaim x c C.L)‖ ≤ Δ₀)

/-- **Acceptance of the abstract protocol** on a coin tuple (steps 1–3 and the final check,
pp.32–33): the initial claim has modulus at most `B_V + 1`; at every layer `i < L` every round
polynomial has degree at most `D`, coefficients of modulus at most `C*`, and computed residual of
modulus at most `6∆₀`; the claimed evaluations have modulus at most `U`; the gate residual has
modulus at most `(K + 3)∆₀`; and the final input residual has modulus at most `4∆₀`.

Das, Gupta, Mondal, More, *Delegating Computation with Approximate Arithmetic* (manuscript,
sha256 78b2a36b…), §C.1, pp.32–33. -/
def AbsAccepts (P : AbsProver C N) (V : AbsVerifier C N) (y : ℂ) (δ BV BW : ℕ) (Δ₀ : ℝ)
    (c : Coins C N) : Prop :=
  ‖y‖ ≤ (BV : ℝ) + 1 ∧
  (∀ i, i < C.L →
    (∀ j, 1 ≤ j → j ≤ C.ki i →
      (P.poly i j c).natDegree ≤ C.Dpar δ ∧
      (∀ a, ‖(P.poly i j c).coeff a‖ ≤ constCstar C.h C.mMax BV BW) ∧
      ‖V.res i j c‖ ≤ 6 * Δ₀) ∧
    ‖(P.claims i c).1‖ ≤ constU C.h C.mMax BV ∧
    ‖(P.claims i c).2‖ ≤ constU C.h C.mMax BV ∧
    ‖V.gres i c‖ ≤ (constK C.h C.mMax BV BW + 3) * Δ₀) ∧
  ‖V.fres c‖ ≤ 4 * Δ₀

end ApproxGKR


