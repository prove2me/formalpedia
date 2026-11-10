-- Prove2me | Definitions.Def_AlmostLinSubsetSum_Main_GAP
-- name    : AlmostLinSubsetSum_Main_GAP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:28:56.419069+00:00
-- url     : https://prove2.me/theorems/4f0b116b-eb3c-492a-a7a5-a0dfe02642a3
-- title:
--   Generalized arithmetic progressions: rank, centered, $P_\lambda$, proper and $\lambda$-proper
-- statement:
--   §9 preamble (p. 41). A **GAP of rank $r$** is described by $(p_0,\Gamma,\rho)$: $p_0\in\mathbb Z$, a box $\Gamma=\prod_{j=1}^r[\gamma_j,\gamma'_j]$ (real endpoints), and an integer homomorphism $\rho:\mathbb Z^r\to\mathbb Z$; the GAP is the set $P=p_0+\rho(\Gamma\cap\mathbb Z^r)$.
--
--   - It is **proper** if $\rho$ is injective on $\Gamma\cap\mathbb Z^r$, and **centered** if $p_0=0$ and $0\in\Gamma$.
--   - For a centered description, $P_\lambda:=\rho(\lambda\cdot\Gamma\cap\mathbb Z^r)$, and the GAP is **$\lambda$-proper** if $P_\lambda$ is proper, i.e. $\rho$ is injective on $\lambda\cdot\Gamma\cap\mathbb Z^r$.
--   - $z+X$ is the translate of a set of integers.
--
--   A GAP is its description: $P_\lambda$ depends on $\Gamma$ and $\rho$, not only on the set $P$.
-- source:
--   Chen, Mao, Zhang (2026), An Almost-Linear Time Algorithm for Multidimensional Subset Sum, STOC 2027 submission, SHA-256 0cd42ca048cfff088013ad06450a278a6df72a29004c48c5c138f3f6df85d1e0, §9, p. 41

import Mathlib
import Definitions.Def_AlmostLinSubsetSum_Main_Basic

set_option autoImplicit false

namespace AlmostLinSubsetSum.Main

/-!
# Generalized arithmetic progressions

Chen, Mao, Zhang (2026), STOC 2027 submission, SHA-256 0cd42ca0…1e0, §9 preamble, p. 41:
"A generalized arithmetic progression (GAP) of rank r is a set of integers described as
P = p₀ + ρ(Γ ∩ ℤ^r), Γ = ∏_{j=1}^r [γ_j, γ'_j], where p₀ ∈ ℤ and ρ : ℤ^r → ℤ is an integer
homomorphism. […] It is proper if ρ is injective on Γ ∩ ℤ^r. It is centered if p₀ = 0 and
0 ∈ Γ […]. For a centered description, define P_λ := ρ(λ · Γ ∩ ℤ^r); the GAP is λ-proper if
P_λ is proper."

**Formalization Note.** A GAP is its *description* `(r, p₀, Γ, ρ)`: `P_λ` depends on `Γ` and
`ρ`, not only on the set `P`. The endpoints `γ_j ≤ γ'_j` of `Γ` are real numbers (the paper
does not require integer endpoints; Lemma 9.2's proof passes to the integer hull). `P_λ` is
defined for every description; the paper uses it for centered ones.
-/

/-- A GAP description of rank `rank`: base point `p₀`, coefficient box
`Γ = ∏_j [lo j, hi j]` (real endpoints) and integer homomorphism `ρ : ℤ^rank → ℤ`. -/
structure GAP where
  rank : ℕ
  base : ℤ
  lo : Fin rank → ℝ
  hi : Fin rank → ℝ
  ρ : (Fin rank → ℤ) →+ ℤ

namespace GAP

/-- The coefficient box `Γ ⊂ ℝ^rank`. -/
def coeffBox (P : GAP) : Set (Fin P.rank → ℝ) := {y | ∀ j, P.lo j ≤ y j ∧ y j ≤ P.hi j}

/-- The integer points of `λ · Γ`. -/
def dilatedPoints (P : GAP) (c : ℝ) : Set (Fin P.rank → ℤ) :=
  {x | toReal x ∈ dilate c P.coeffBox}

/-- The set `P = p₀ + ρ(Γ ∩ ℤ^r)` of integers. -/
def carrier (P : GAP) : Set ℤ := (fun x => P.base + P.ρ x) '' P.dilatedPoints 1

/-- Proper: `ρ` is injective on `Γ ∩ ℤ^r`. -/
def IsProper (P : GAP) : Prop := Set.InjOn P.ρ (P.dilatedPoints 1)

/-- Centered: `p₀ = 0` and `0 ∈ Γ`. -/
def IsCentered (P : GAP) : Prop := P.base = 0 ∧ ∀ j, P.lo j ≤ 0 ∧ 0 ≤ P.hi j

/-- `P_λ := ρ(λ · Γ ∩ ℤ^r)`. -/
def dilateSet (P : GAP) (c : ℝ) : Set ℤ := P.ρ '' P.dilatedPoints c

/-- `λ`-proper: `P_λ` is proper, i.e. `ρ` is injective on `λ · Γ ∩ ℤ^r`. -/
def IsDilateProper (P : GAP) (c : ℝ) : Prop := Set.InjOn P.ρ (P.dilatedPoints c)

end GAP

/-- The translate `z + X` of a set of integers. -/
def intTranslate (z : ℤ) (X : Set ℤ) : Set ℤ := (fun x => z + x) '' X

end AlmostLinSubsetSum.Main


