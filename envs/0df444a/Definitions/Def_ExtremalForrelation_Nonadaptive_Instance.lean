-- Prove2me | Definitions.Def_ExtremalForrelation_Nonadaptive_Instance
-- name    : ExtremalForrelation_Nonadaptive_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:55:39.244193+00:00
-- url     : https://prove2.me/theorems/28e7a5ad-9ada-4cb4-82d4-75ddd49b53d1
-- title:
--   The hard instances $(\chi_f,\chi_g)$, the transcript laws $\mu_s$ and $\rho$ and their conditional versions, and $r$-good subspaces
-- statement:
--   Fix $n$ with $m=n/2$, a subspace $K$ of $\mathbb F_2^n$, and a set $Q\subseteq\mathbb F_2^n$ of query points. Write $C$ for a coset of $K$ and $D$ for a coset of $K^\perp$, and $\phi_C$, $\psi_D$ for their representatives (smallest binary value).
--
--   1. **Pairing and bits.** $\pi$ is a bijection from the cosets of $K$ to the cosets of $K^\perp$ (it pairs $C$ with $\pi(C)$), and $h$ assigns a bit to every coset of $K$. For a bit $s$,
--   $$\bar h(D)=h(\pi^{-1}(D))+\langle\phi_{\pi^{-1}(D)},\psi_D\rangle+s .\tag{1}$$
--   2. **The functions.** For a bit function $\bar h$ on the cosets of $K^\perp$,
--   $$f(x)=\langle x,\psi_{\pi(C)}\rangle+h(C)\ \ (x\in C),\qquad g(y)=\langle\phi_{\pi^{-1}(D)},y\rangle+\bar h(D)\ \ (y\in D).\tag{2–3}$$
--   The instance with secret bit $s$ uses $\bar h$ from (1); the oracles are $\chi_f,\chi_g$.
--   3. **Transcripts.** The transcript of $(f,g)$ at $Q$ is $\tau=(f(x),g(x))_{x\in Q}$.
--   4. **Laws.** $\mu_s(\tau\mid K,\pi)$ is the probability that the transcript equals $\tau$ when $h$ is uniform and $\bar h$ is given by (1). $\rho(\tau\mid K,\pi)$ is the same with $h$ and $\bar h$ uniform and independent. $\mu_s(\cdot\mid K)$ and $\rho(\cdot\mid K)$ average these over a uniform bijection $\pi$. $\mu_s$ and $\rho$ average those over $K$ uniform among the $m$-dimensional subspaces. So $K$, $\pi$, $h$ (and $\bar h$ under $\rho$) are independent and uniform.
--   5. **Goodness (Definition 6).** For $r\ge1$, $K$ is **$r$-good for $Q$** if for every coset $C$ of $K$ and every coset $C$ of $K^\perp$,
--   $$\dim\operatorname{span}\{x+x' : x,x'\in Q\cap C\}\le r .$$
--
--   These are the hard instances of §1.1.1 (p. 4), the reference law of §1.1.2 (p. 5) and the conditional laws of §3.4 (p. 12). Every later statement about $\mu_s$ and $\rho$ refers to these exact draws.
--
--   **Formalization Note.** The paper enumerates the cosets as $C_1,\dots,C_M$, $D_1,\dots,D_M$ and draws a uniform permutation of $[M]$. Transported along the enumerations this is a uniform bijection between the quotient types `V n ⧸ K` and `V n ⧸ orth K`, which is what the Lean uses; $h$ is a function on `V n ⧸ K`. Transcripts are bit-valued (`Q → ZMod 2 × ZMod 2`), a bijective encoding of the $\pm1$ answers. Every law is a finite uniform average.
-- source:
--   Clément Canonne, Kenny Chen, Julian Mestre, STOC 2027 submission #61 (October 2026), §1.1.1 p. 4 eqs. (1)–(3), §1.1.2 p. 5 (ρ), p. 3 (transcripts), §3.4 p. 12 (conditional laws), Definition 6 p. 12, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/61.pdf

import Mathlib
import Definitions.Def_ExtremalForrelation_Nonadaptive_Basic

open Classical

noncomputable section

namespace ExtremalForrelation.Nonadaptive

/-!
# The hard instances and the transcript laws `μ_s`, `ρ`

Canonne–Chen–Mestre, STOC 2027 submission #61 (October 2026), §1.1.1 p. 4 (equations (1)–(3)),
§1.1.2 p. 5 (the reference law `ρ`), p. 3 (transcripts), §3.4 p. 12 (conditional laws),
Definition 6 p. 12 (goodness).

The cosets of `K` are the elements of the quotient `V n ⧸ K`; those of `K^⊥` are the elements of
`V n ⧸ orth K`. The paper enumerates each family as `C_1, …, C_M`, `D_1, …, D_M` in a fixed way
and draws a uniform permutation `π` of `[M]`; transported along the two fixed enumerations this
is exactly a uniform bijection `π : V n ⧸ K ≃ V n ⧸ orth K` pairing `C` with `π C`, and the
random bits `h : [M] → 𝔽₂` become `h : V n ⧸ K → 𝔽₂`. Representatives `φ_i`, `ψ_j` are the
smallest elements as binary numbers (`rep`).
-/

/-- `h̄(j) = h(π⁻¹(j)) + ⟨φ_{π⁻¹(j)}, ψ_j⟩ + s`, equation (1), p. 4. -/
def hbarOf {n : ℕ} (K : Submodule (ZMod 2) (V n)) (π : (V n ⧸ K) ≃ (V n ⧸ orth K))
    (h : V n ⧸ K → ZMod 2) (s : ZMod 2) (D : V n ⧸ orth K) : ZMod 2 :=
  h (π.symm D) + dot (rep K (π.symm D)) (rep (orth K) D) + s

/-- `f(x) = ⟨x, ψ_{π(i)}⟩ + h(i)` for `x ∈ C_i`, equation (2), p. 4. -/
def fFun {n : ℕ} (K : Submodule (ZMod 2) (V n)) (π : (V n ⧸ K) ≃ (V n ⧸ orth K))
    (h : V n ⧸ K → ZMod 2) (x : V n) : ZMod 2 :=
  dot x (rep (orth K) (π (Submodule.Quotient.mk x))) + h (Submodule.Quotient.mk x)

/-- `g(y) = ⟨φ_{π⁻¹(j)}, y⟩ + h̄(j)` for `y ∈ D_j`, equation (3), p. 4, for a given bit
function `h̄` on the cosets of `K^⊥`. -/
def gFun {n : ℕ} (K : Submodule (ZMod 2) (V n)) (π : (V n ⧸ K) ≃ (V n ⧸ orth K))
    (hb : V n ⧸ orth K → ZMod 2) (y : V n) : ZMod 2 :=
  dot (rep K (π.symm (Submodule.Quotient.mk y))) y + hb (Submodule.Quotient.mk y)

/-- A transcript at the query set `Q`: the pair of answers `(f(x), g(x))` at every queried
point (p. 3), in bit encoding (the oracles return `χ_f(x) = (−1)^{f(x)}`, `χ_g(x)`). -/
abbrev Transcript {n : ℕ} (Q : Finset (V n)) : Type := Q → ZMod 2 × ZMod 2

/-- The transcript of the pair `(f, g)` at the query set `Q`. -/
def transcript {n : ℕ} (Q : Finset (V n)) (f g : V n → ZMod 2) : Transcript Q :=
  fun x => (f x.1, g x.1)

/-- `μ_s(τ | K, π)`: probability of transcript `τ` when `h` is uniform and `h̄` is set by (1). -/
def muKP {n : ℕ} (Q : Finset (V n)) (s : ZMod 2) (K : Submodule (ZMod 2) (V n))
    (π : (V n ⧸ K) ≃ (V n ⧸ orth K)) (τ : Transcript Q) : ℝ :=
  uprob (fun h : V n ⧸ K → ZMod 2 =>
    transcript Q (fFun K π h) (gFun K π (hbarOf K π h s)) = τ)

/-- `ρ(τ | K, π)`: probability of `τ` when `h` and `h̄` are uniform and independent (p. 5). -/
def rhoKP {n : ℕ} (Q : Finset (V n)) (K : Submodule (ZMod 2) (V n))
    (π : (V n ⧸ K) ≃ (V n ⧸ orth K)) (τ : Transcript Q) : ℝ :=
  uprob (fun hh : (V n ⧸ K → ZMod 2) × (V n ⧸ orth K → ZMod 2) =>
    transcript Q (fFun K π hh.1) (gFun K π hh.2) = τ)

/-- `μ_s(τ | K)`: `π` uniform among the bijections, then `h` uniform. -/
def muK {n : ℕ} (Q : Finset (V n)) (s : ZMod 2) (K : Submodule (ZMod 2) (V n))
    (τ : Transcript Q) : ℝ :=
  uavg ((V n ⧸ K) ≃ (V n ⧸ orth K)) (fun π => muKP Q s K π τ)

/-- `ρ(τ | K)`: `π` uniform, then `h`, `h̄` uniform and independent. -/
def rhoK {n : ℕ} (Q : Finset (V n)) (K : Submodule (ZMod 2) (V n)) (τ : Transcript Q) : ℝ :=
  uavg ((V n ⧸ K) ≃ (V n ⧸ orth K)) (fun π => rhoKP Q K π τ)

/-- `μ_s(τ)`: the transcript law of the instance with secret bit `s`, with `K` uniform among
the `n/2`-dimensional subspaces, and `π`, `h` uniform and independent (§1.1.1). -/
def mu {n : ℕ} (Q : Finset (V n)) (s : ZMod 2) (τ : Transcript Q) : ℝ :=
  uavg (Grass n) (fun K => muK Q s K.1 τ)

/-- `ρ(τ)`: the reference transcript law (p. 5). -/
def rho {n : ℕ} (Q : Finset (V n)) (τ : Transcript Q) : ℝ :=
  uavg (Grass n) (fun K => rhoK Q K.1 τ)

/-- The differences `{x + x' : x, x' ∈ Q ∩ c}` of the queries in a coset `c` of `W`. -/
def diffSet {n : ℕ} (Q : Finset (V n)) (W : Submodule (ZMod 2) (V n)) (c : V n ⧸ W) :
    Set (V n) :=
  {z | ∃ x ∈ Q, ∃ x' ∈ Q, Submodule.Quotient.mk x = c ∧ Submodule.Quotient.mk x' = c ∧
    z = x + x'}

/-- Definition 6 (p. 12): `K` is `r`-good for `Q` if for every coset `C` of `K` or of `K^⊥`,
`dim span{x + x' : x, x' ∈ Q ∩ C} ≤ r`. -/
def IsGood {n : ℕ} (Q : Finset (V n)) (r : ℕ) (K : Submodule (ZMod 2) (V n)) : Prop :=
  (∀ c : V n ⧸ K, Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (diffSet Q K c)) ≤ r) ∧
  (∀ d : V n ⧸ orth K,
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (diffSet Q (orth K) d)) ≤ r)

end ExtremalForrelation.Nonadaptive


