-- Prove2me | Definitions.Def_QuadraticRE_CompPrivate
-- name    : QuadraticRE_CompPrivate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:18:26.442912+00:00
-- url     : https://prove2.me/theorems/efd94dec-c752-4fc9-bd0a-85787bda6961
-- title:
--   Negligible functions, nonuniform distinguishers and computational privacy
-- statement:
--   A function $\nu:\mathbb N\to\mathbb R$ is **negligible** if for every constant $c>0$, $\nu(\kappa)<\kappa^{-c}$ for all sufficiently large $\kappa$. A **nonuniform probabilistic polynomial-time distinguisher** is a fixed polynomial-time machine together with an advice string $a_\kappa$ and a coin length $\tau_\kappa$, both bounded by a polynomial in $\kappa$; it accepts an encoding $z$ with coins $\omega$ if the machine, on $(1^\kappa,a_\kappa,z,\omega)$, outputs a string starting with $1$. A family $(E_\kappa,f_\kappa,\mathrm{Sim}_\kappa)$ of encodings with simulators on uniform coins is **computationally private** if, for every sequence of inputs $x_\kappa$ and every such distinguisher, the difference between the acceptance probabilities on $E_\kappa(x_\kappa;r)$ and on $\mathrm{Sim}_\kappa(f_\kappa(x_\kappa);\omega')$ is negligible in $\kappa$.
--
--   This is the computational notion in the second paragraph of Lemma 4.11.
--
--   **Formalization Note** The page takes $\nu$ with values in $[0,1]$; no range is imposed here, because Lemma 4.11 applies the notion to $M\varepsilon_\lambda$, which can exceed one at small $\lambda$. The two families named here are the family $H_\kappa$ given by a sequence of cubic descriptions, and the family produced from it by the transformation of Lemma 4.11.
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), §3.1, p.13; Definition 3.7, pp.15–16; Lemma 4.11, p.29

import Mathlib
import Definitions.Def_QuadraticRE_Construction

namespace QuadraticRE

/-- Negligible, Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), §3.1, p.13: for every constant `c > 0`, `ν(λ) < λ^{−c}` for all sufficiently large
`λ`.

**Formalization Note.** The page takes `ν` with values in `[0, 1]`. No range is imposed here, because
Lemma 4.11 applies the word to `Mε_λ`, which may exceed one at small `λ`. -/
def Negligible (ν : ℕ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ᶠ κ : ℕ in Filter.atTop, ν κ < (κ : ℝ) ^ (-c)

/-- A nonuniform probabilistic polynomial-time distinguisher, §3.1, p.13: one fixed polynomial-time
machine, an advice sequence and a coin length, both polynomially bounded. -/
structure Distinguisher where
  D : List Bool → List Bool
  hD : PolyTimeFn id D
  advice : ℕ → List Bool
  coins : ℕ → ℕ
  bound : Polynomial ℕ
  advice_le : ∀ κ, (advice κ).length ≤ bound.eval κ
  coins_le : ∀ κ, coins κ ≤ bound.eval κ

/-- The distinguisher accepts `z` with coins `ω`: the machine on `(1^κ, a_κ, z, ω)` outputs a string
that starts with `1`. -/
def Distinguisher.Accepts (A : Distinguisher) (κ : ℕ) (z : List Bool) (ω : Fin (A.coins κ) → F2) : Prop :=
  (A.D (encNat κ ++ encNat (A.advice κ).length ++ A.advice κ ++ encNat z.length ++ z ++ bits ω)).head?
    = some true

/-- A family of encodings with simulators on uniform coins, indexed by the security parameter. -/
structure EncFamily where
  N : ℕ → ℕ
  ρ : ℕ → ℕ
  ℓ : ℕ → ℕ
  b : ℕ → ℕ
  τ : ℕ → ℕ
  E : ∀ κ, (Fin (N κ) → F2) → (Fin (ρ κ) → F2) → Fin (ℓ κ) → F2
  f : ∀ κ, (Fin (N κ) → F2) → Fin (b κ) → F2
  sim : ∀ κ, (Fin (b κ) → F2) → (Fin (τ κ) → F2) → Fin (ℓ κ) → F2

/-- Computational privacy of a family, Definition 3.7, p.16 (with the conventions for ordinary REs):
for every input sequence and every nonuniform PPT distinguisher, the advantage between the real and the
simulated encoding is negligible. -/
def CompPrivate (F : EncFamily) : Prop :=
  ∀ (xs : ∀ κ, Fin (F.N κ) → F2) (A : Distinguisher),
    Negligible fun κ =>
      |prob (fun ω : (Fin (F.ρ κ) → F2) × (Fin (A.coins κ) → F2) =>
          A.Accepts κ (bits (F.E κ (xs κ) ω.1)) ω.2)
        - prob (fun ω : (Fin (F.τ κ) → F2) × (Fin (A.coins κ) → F2) =>
          A.Accepts κ (bits (F.sim κ (F.f κ (xs κ)) ω.1)) ω.2)|

/-- The family of encodings `H_κ` given by a sequence of descriptions. -/
def cubicFamily (q : ℕ → CubicInput) (b τ : ℕ → ℕ)
    (f : ∀ κ, (Fin (q κ).N → F2) → Fin (b κ) → F2)
    (sim : ∀ κ, (Fin (b κ) → F2) → (Fin (τ κ) → F2) → Fin (q κ).ℓ → F2) : EncFamily where
  N κ := (q κ).N
  ρ κ := (q κ).r
  ℓ κ := (q κ).ℓ
  b := b
  τ := τ
  E κ x r := (q κ).D.eval x r
  f := f
  sim := sim

/-- The family produced by the transformation of Lemma 4.11 on a sequence of descriptions: the encoder
is `D′`, and the simulator runs `sim` on the first `τ` coins and `post` on its output and the other `τ′`
coins. -/
def transformedFamily (T : ∀ q : CubicInput, CubicOutput q.N q.ℓ) (q : ℕ → CubicInput) (b τ : ℕ → ℕ)
    (f : ∀ κ, (Fin (q κ).N → F2) → Fin (b κ) → F2)
    (sim : ∀ κ, (Fin (b κ) → F2) → (Fin (τ κ) → F2) → Fin (q κ).ℓ → F2) : EncFamily where
  N κ := (q κ).N
  ρ κ := (T (q κ)).ρ'
  ℓ κ := (T (q κ)).ℓ'
  b := b
  τ κ := τ κ + (T (q κ)).τ'
  E κ x r := (T (q κ)).D'.eval x r
  f := f
  sim κ y ω := (T (q κ)).post.eval
    (Sum.elim (sim κ y (fun i => ω (Fin.castAdd _ i))) (fun i => ω (Fin.natAdd _ i)))

end QuadraticRE


