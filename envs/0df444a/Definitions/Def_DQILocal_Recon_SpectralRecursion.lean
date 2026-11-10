-- Prove2me | Definitions.Def_DQILocal_Recon_SpectralRecursion
-- name    : DQILocal_Recon_SpectralRecursion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:05:52.531242+00:00
-- url     : https://prove2.me/theorems/d18f0a60-a096-42e1-817e-da9717344a0d
-- title:
--   The spectral recursion $V^{(t)},C^{(t)},N^{(t)}$ and $P_t=\mathbb E\,S(N^{(t)})$ (Definition 4.2)
-- statement:
--   Let $p$ be a spectrum (in the paper, the Gibbs weights $p_\beta$). The **random check-node operation** $\Gamma(\lambda,\mu)=\nu_\Delta$ draws a label $\Delta$ with law $P_{\lambda,\mu}$; for several arguments $\Gamma(\lambda_1)=\lambda_1$ and $\Gamma(\lambda_1,\dots,\lambda_h)=\Gamma(\Gamma(\lambda_1,\dots,\lambda_{h-1}),\lambda_h)$ with fresh randomness at each step.
--
--   The **spectral recursion** for the $(k,D)$ tree is the sequence of random spectra
--
--   $$V^{(0)}=p,\qquad C^{(t)}=R\,\Gamma\bigl(V^{(t)}_1,\dots,V^{(t)}_{D-1}\bigr),\qquad V^{(t+1)}=p*C^{(t)}_1*\cdots*C^{(t)}_{k-1},$$
--
--   where the arguments on each right-hand side are independent copies. The root spectrum is $N^{(0)}=p$ and $N^{(t)}=p*C^{(t-1)}_1*\cdots*C^{(t-1)}_k$ for $t\ge1$, and
--
--   $$P_t=\mathbb E\,S\bigl(N^{(t)}\bigr),\qquad P_\infty=\lim_{t\to\infty}P_t .$$
--
--   $P_t$ is the optimal success probability for the root of the depth-$t$ tree code (Proposition 4.3); the definition here is the recursion itself, independent of any measurement.
--
--   **Formalization Note** Every law in the recursion takes finitely many values, so a law is a finite list of (probability, spectrum) pairs (`FinLaw`), with explicit bind, pushforward, probability and expectation; independence is a product of separate sums. `Pt k D q f β t` is $P_t$ at $p=p_\beta$. $P_\infty$ is written as $\sup_tP_t$, which equals the limit because $P_t$ is nondecreasing and at most one.
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), Definition 4.2, p. 24 (Γ: p. 24; P_∞: Theorem 5.2, p. 30)

import Mathlib
import Definitions.Def_DQILocal_Recon_Spectra

namespace DQILocal.Recon

open scoped BigOperators

/-- **Finitely supported laws of spectra.**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), Definition 4.2, p. 24
(the random spectra `V^{(t)}`, `C^{(t)}`, `N^{(t)}` take finitely many values).

A `FinLaw q` is a finite list of pairs `(w, ν)`: the spectrum `ν` occurs with probability `w`
(repeated values add up). Every law built in this file has nonnegative weights summing to one.

**Formalization Note.** A list rather than `PMF` keeps every operation an explicit finite sum. Two
lists describe the same law when they give every set the same total weight (`FinLaw.prob`); only
`FinLaw.prob` and `FinLaw.expect` are used in statements. -/
abbrev FinLaw (q : ℕ) := List (ℝ × (ZMod q → ℝ))

namespace FinLaw

variable {q : ℕ}

/-- The point mass at `ν`. -/
def dirac (ν : ZMod q → ℝ) : FinLaw q := [(1, ν)]

/-- `L.bind K`: draw `ν` from `L`, then draw from the law `K ν` (weights multiply). -/
def bind (L : FinLaw q) (K : (ZMod q → ℝ) → FinLaw q) : FinLaw q :=
  L.flatMap fun a => (K a.2).map fun b => (a.1 * b.1, b.2)

/-- Image of a law under a map of spectra. -/
def pushforward (g : (ZMod q → ℝ) → (ZMod q → ℝ)) (L : FinLaw q) : FinLaw q :=
  L.map fun a => (a.1, g a.2)

/-- Expectation `E[g(ν)]` of a real function of the spectrum. -/
def expect (L : FinLaw q) (g : (ZMod q → ℝ) → ℝ) : ℝ :=
  (L.map fun a => a.1 * g a.2).sum

/-- Probability `Pr[ν ∈ A]`. -/
noncomputable def prob (L : FinLaw q) (A : Set (ZMod q → ℝ)) : ℝ := by
  classical
  exact (L.map fun a => if a.2 ∈ A then a.1 else 0).sum

/-- Law of `λ₁ ∗ ⋯` folded with independent draws: `convFold ν [L₁, …, L_h]` is the law of
`ν ∗ X₁ ∗ ⋯ ∗ X_h` with `X_j ~ L_j` independent. -/
noncomputable def convFold [NeZero q] (ν : ZMod q → ℝ) (Ls : List (FinLaw q)) : FinLaw q :=
  Ls.foldl (fun acc L => acc.bind fun lam => L.bind fun mu => dirac (conv lam mu)) (dirac ν)

end FinLaw

/-- The random check-node operation `Γ(λ, μ) = ν_Δ` with `Δ ~ P_{λ,μ}` (p. 24), as a law. -/
noncomputable def gammaLaw {q : ℕ} [NeZero q] (lam mu : ZMod q → ℝ) : FinLaw q :=
  (Finset.univ : Finset (ZMod q)).toList.map fun δ => (labelProb lam mu δ, nuDelta lam mu δ)

/-- `Γ(λ₁, …, λ_h)` with `λ_j ~ L_j` independent and fresh randomness at every step:
`Γ(λ₁) = λ₁`, `Γ(λ₁, …, λ_h) = Γ(Γ(λ₁, …, λ_{h-1}), λ_h)` (p. 24). The empty list is not used
(`h = D - 1 ≥ 1`). -/
noncomputable def gammaFold {q : ℕ} [NeZero q] : List (FinLaw q) → FinLaw q
  | [] => []
  | L :: Ls => Ls.foldl (fun acc L' => acc.bind fun lam => L'.bind fun mu => gammaLaw lam mu) L

/-- **The spectral recursion (Definition 4.2, p. 24)**, for the `(k, D)` tree and the channel
spectrum `p`:
`V^{(0)} = δ_p`, `C^{(t)} = R Γ(V₁^{(t)}, …, V_{D-1}^{(t)})`,
`V^{(t+1)} = p ∗ C₁^{(t)} ∗ ⋯ ∗ C_{k-1}^{(t)}`, all arguments independent copies.
`specV k D p t` is the law of `V^{(t)}`. -/
noncomputable def specV {q : ℕ} [NeZero q] (k D : ℕ) (p : ZMod q → ℝ) : ℕ → FinLaw q
  | 0 => FinLaw.dirac p
  | t + 1 => FinLaw.convFold p (List.replicate (k - 1)
      (FinLaw.pushforward refl (gammaFold (List.replicate (D - 1) (specV k D p t)))))

/-- The law of `C^{(t)} = R Γ(V₁^{(t)}, …, V_{D-1}^{(t)})` (Definition 4.2, p. 24). -/
noncomputable def specC {q : ℕ} [NeZero q] (k D : ℕ) (p : ZMod q → ℝ) (t : ℕ) : FinLaw q :=
  FinLaw.pushforward refl (gammaFold (List.replicate (D - 1) (specV k D p t)))

/-- The law of the root spectrum: `N^{(0)} = δ_p` and
`N^{(t)} = p ∗ C₁^{(t-1)} ∗ ⋯ ∗ C_k^{(t-1)}` for `t ≥ 1` (Definition 4.2, p. 24). -/
noncomputable def specN {q : ℕ} [NeZero q] (k D : ℕ) (p : ZMod q → ℝ) : ℕ → FinLaw q
  | 0 => FinLaw.dirac p
  | t + 1 => FinLaw.convFold p (List.replicate k (specC k D p t))

/-- `P_t = E S(N^{(t)})` (Definition 4.2, p. 24) for a general channel spectrum `p`. -/
noncomputable def Pspec {q : ℕ} [NeZero q] (k D : ℕ) (p : ZMod q → ℝ) (t : ℕ) : ℝ :=
  (specN k D p t).expect succFn

/-- `P_t` at the Gibbs weights `p_β` of the cost `f` (Definition 4.2 with `p = p_β`, p. 24). -/
noncomputable def Pt (k D q : ℕ) [NeZero q] (f : ZMod q → ℝ) (β : ℝ) (t : ℕ) : ℝ :=
  Pspec k D (gibbsWeight q f β) t

/-- `P_∞ = lim_{t→∞} P_t`, written as `sup_t P_t` (Theorem 5.2, p. 30).

**Formalization Note.** `P_t` is nondecreasing and at most one (Proposition 4.3), so the supremum is
the limit; the supremum of a real sequence bounded above is the true one. -/
noncomputable def Pinf (k D q : ℕ) [NeZero q] (f : ZMod q → ℝ) (β : ℝ) : ℝ :=
  ⨆ t : ℕ, Pt k D q f β t

end DQILocal.Recon


