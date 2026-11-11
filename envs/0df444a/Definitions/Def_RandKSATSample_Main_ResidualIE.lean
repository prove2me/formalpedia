-- Prove2me | Definitions.Def_RandKSATSample_Main_ResidualIE
-- name    : RandKSATSample_Main_ResidualIE
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:59:59.353534+00:00
-- url     : https://prove2.me/theorems/49e6f354-69f5-4bf3-85c6-cdb340536abb
-- title:
--   The quantities of the inclusion–exclusion identity: CS_F(a), N_F[S], F_S, w_S and η_S (5.1)
-- statement:
--   In §5 the family is $\mathcal F=\mathcal C^{\mathrm{good}}$, the bad event $B_a$ of $a$ is the violation $E_a$ of its residual clause, and $H$ is the graph on $\mathcal F$ joining constraints that share a variable ($=H_\Psi$). For $F\subseteq\mathcal F$ and $a\in F$, $\mathsf{CS}_F(a)$ is the set of connected subsets of $H[F]$ containing $a$, and for $S\in\mathsf{CS}_F(a)$ (5.1):
--   $$F^-=F\setminus\{a\},\quad F_S=F\setminus N_F[S],\quad w_S=q_S\frac{Z_{F_S}}{Z_{F^-}},\quad \eta_S=\nu_{\mathrm{good}}(\cdot\mid E_S\cap\mathrm{Good}(F_S)),$$
--   where $N_F[S]$ is the closed neighbourhood of $S$ in $H[F]$ and $E_S=\bigcap_{c\in S}E_c$.
--
--   **Formalization Note.** $\eta_S(A)$ is the ratio $\nu_{\mathrm{good}}(A\cap E_S\cap\mathrm{Good}(F_S))/\nu_{\mathrm{good}}(E_S\cap\mathrm{Good}(F_S))$, set to $0$ when the denominator is $0$; then $w_S=0$ as well, so the convention never enters a sum with nonzero weight.
-- source:
--   He, Li, Yang, Fast Almost-Uniform Sampling of Random k-SAT Solutions, arXiv:2610.10474 (version not printed; file sha256 563a4d84…), §5 opening, p. 37, (5.1)

import Mathlib
import Definitions.Def_RandKSATSample_Main_Structure

set_option autoImplicit false

open scoped BigOperators

namespace RandKSATSample.Main

noncomputable section

open Classical

/-!
# The quantities of the inclusion–exclusion identity (5.1)

He, Li, Yang, *Fast Almost-Uniform Sampling of Random k-SAT Solutions*, arXiv:2610.10474
(version not printed; file sha256 563a4d84…), §5 opening, p. 37, (5.1).

The family of §5 is `𝓕 = C_good`, the bad event `B_a` is the violation `E_a` of the residual
clause `C_a^good`, and the graph `H` on `𝓕` (constraints sharing a good variable) is `H_Ψ`.
For `F ⊆ 𝓕` the induced graph `H[F]` has the closed neighbourhood `N_F[S]`.
-/

variable {n m k : ℕ}

/-- `CS_F(a)`: the connected subsets of `H[F]` containing `a`. -/
def CSin (Φ : Formula n m k) (F : Finset (Fin m)) (a : Fin m) : Finset (Finset (Fin m)) :=
  F.powerset.filter fun S => a ∈ S ∧ IsConnectedSet (HPsi Φ) S

/-- `N_F[S]`, the closed neighbourhood of `S` in `H[F]`. -/
def nbhdIn (Φ : Formula n m k) (F S : Finset (Fin m)) : Finset (Fin m) :=
  S ∪ F.filter fun b => ∃ c ∈ S, (HPsi Φ).Adj c b

/-- `F_S = F ∖ N_F[S]`. -/
def FS (Φ : Formula n m k) (F S : Finset (Fin m)) : Finset (Fin m) := F \ nbhdIn Φ F S

/-- `w_S = q_S Z_{F_S} / Z_{F⁻}`, `F⁻ = F ∖ {a}`. -/
def wS (Φ : Formula n m k) (F : Finset (Fin m)) (a : Fin m) (S : Finset (Fin m)) : ℝ :=
  qS Φ S * Zf Φ (FS Φ F S) / Zf Φ (F.erase a)

/-- `η_S(A) = ν_good(A | E_S ∩ Good(F_S))` (the value `0` when the conditioning event is null,
in which case `w_S = 0`). -/
def etaS (Φ : Formula n m k) (F S : Finset (Fin m)) (A : PartAssign n (Vgood Φ) → Prop) : ℝ :=
  nuGood Φ (fun τ => A τ ∧ (∀ c ∈ S, Viol Φ c τ) ∧ GoodEv Φ (FS Φ F S) τ) /
    nuGood Φ (fun τ => (∀ c ∈ S, Viol Φ c τ) ∧ GoodEv Φ (FS Φ F S) τ)

end

end RandKSATSample.Main


