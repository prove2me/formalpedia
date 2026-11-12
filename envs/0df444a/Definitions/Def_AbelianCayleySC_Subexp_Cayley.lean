-- Prove2me | Definitions.Def_AbelianCayleySC_Subexp_Cayley
-- name    : AbelianCayleySC_Subexp_Cayley
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:42:51.684194+00:00
-- url     : https://prove2.me/theorems/e26def18-2204-41cd-b84d-8ea80adc1af2
-- title:
--   Abelian Cayley graphs, characters, $\lambda(\chi)$, $\mathrm{mul}_\tau$, $\eta_\chi$, $|\cdot|_q$, $\mathrm{Sweep}(\chi)$ and $\beta(\chi)$
-- statement:
--   Let $\Gamma$ be a finite abelian group, written additively, and $S\subseteq\Gamma$. The **Cayley graph** $\mathrm{Cay}(\Gamma,S)$ has vertex set $\Gamma$ and $x\sim y$ iff $y-x\in S$; it is $|S|$-regular, has a self-loop at every vertex iff $0\in S$, and need not be connected. $S$ is **symmetric** if $S=-S$, which makes the graph undirected.
--
--   A **character** is a homomorphism $\chi:\Gamma\to\mathbb C^\times$; the characters form the dual group $\widehat\Gamma$ under pointwise multiplication, with the trivial character $1$. For $\chi$ of order $m$:
--
--   1. $\alpha(\chi)=\frac1{|S|}\sum_{s\in S}\chi(s)$ and $\lambda(\chi)=1-\alpha(\chi)$;
--   2. $\mathrm{low}_\tau=\{\chi\in\widehat\Gamma:\lambda(\chi)\le\tau\}$ and $\mathrm{mul}_\tau=|\mathrm{low}_\tau|$;
--   3. $\eta_\chi(x)\in\{0,\dots,m-1\}$ is the $j$ with $\chi(x)=e^{2\pi i j/m}$;
--   4. the **modular distance** is $|a|_q=\min_{k\in\mathbb Z}|a-kq|$;
--   5. the **threshold rounding** of $\chi$ is $\mathrm{Sweep}(\chi)=\{x\in\Gamma:\chi(x)=e^{2\pi i j/m}\text{ for some integer }0\le j<\lfloor m/2\rfloor\}=\eta_\chi^{-1}(\{0,\dots,\lfloor m/2\rfloor-1\})$;
--   6. $$\beta(\chi)=\frac{\mathbb E_{s\sim S}\big[|\eta_\chi(s)|_m\big]}{m},$$ where $\mathbb E_{s\sim S}$ is the uniform average over $S$.
--
--   These are the objects of the paper's character-rounding analysis (§§2–4).
--
--   **Formalization Note** Characters are Mathlib's `AddChar Γ ℂ`, so the paper's $\chi+\gamma$, $k\chi$, $-\chi$ are `χ * γ`, `χ ^ k`, `χ⁻¹`, and the order is `orderOf χ`. Because $\alpha(\chi)$ is real for symmetric $S$, $\lambda(\chi)$ is stored as the real number $1-\operatorname{Re}\alpha(\chi)$. The value $\eta_\chi(x)$ is chosen among $j<m$ by `Classical.choose`, with a default $0$ that is never reached because every value of a character of order $m$ is an $m$-th root of unity; that fact is proof work, not part of the definition. The printed threshold "$\lfloor m\rfloor/2\rfloor-1$" (pp.4, 8) has a stray bracket and is read as $\lfloor m/2\rfloor-1$, as the sentence after it on p.8 states. $1/|S|$ is Lean's division, $0$ when $S=\emptyset$.
-- source:
--   Jake Ruotolo, Sparsest Cut on Abelian Cayley Graphs, STOC 2027 submission #1724 (October 2026), §2 p.3 (low_τ, mul_τ); §2.1 p.4 and §4 p.8 (Sweep); §3 pp.6–7 ((3.1), modular distance, Cayley graphs, Fact 3.3 α and λ); §4.2 p.10 (β)

import Mathlib
import Definitions.Def_AbelianCayleySC_Subexp_RegularGraph

namespace AbelianCayleySC.Subexp

open Finset

/-!
# Abelian Cayley graphs, characters, threshold rounding

Jake Ruotolo, *Sparsest Cut on Abelian Cayley Graphs*, STOC 2027 submission #1724 (October 2026),
§2 p.3 (`low_τ`, `mul_τ`), §2.1 p.4 and §4 p.8 (`Sweep`), §3 pp.6–7 (characters, (3.1), modular
distance, Cayley graphs, Fact 3.3), §4.2 p.10 (`β`).

**Notation.** The paper writes the dual group `Γ̂` additively. Here a character is Mathlib's
`AddChar Γ ℂ`, a commutative group under pointwise multiplication: the paper's `χ + γ` is
`χ * γ`, `kχ` is `χ ^ k`, `−χ` is `χ⁻¹`, and the trivial character is `1`.
The order `ord(χ)` is `orderOf χ`.
-/

variable {Γ : Type} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]

/-- The Cayley graph `Cay(Γ, S)`: `x ~ y` iff `y − x ∈ S` (§3, p.7). A self-loop at every vertex
exactly when `0 ∈ S`; `S` need not generate `Γ`. -/
def cayAdj (S : Finset Γ) : Γ → Γ → Prop := fun x y => y - x ∈ S

instance (S : Finset Γ) : DecidableRel (cayAdj S) := fun x y =>
  inferInstanceAs (Decidable (y - x ∈ S))

/-- `S` is symmetric, `S = −S`, i.e. `Cay(Γ, S)` is undirected (§3, p.7). -/
def IsSymmetricSet (S : Finset Γ) : Prop := ∀ s ∈ S, -s ∈ S

/-- `α(χ) = (1/|S|) ∑_{s ∈ S} χ(s)`, the eigenvalue of `A(G)` on the character `χ` (Fact 3.3). -/
noncomputable def charAlpha (S : Finset Γ) (χ : AddChar Γ ℂ) : ℂ :=
  (1 / (S.card : ℂ)) * ∑ s ∈ S, χ s

/-- `λ(χ) = 1 − α(χ)`, the eigenvalue of `L(G)` on `χ` (Fact 3.3). For symmetric `S`, `α(χ)` is
real, so `λ(χ)` is stored as the real number `1 − Re α(χ)`. -/
noncomputable def charLam (S : Finset Γ) (χ : AddChar Γ ℂ) : ℝ :=
  1 - (charAlpha S χ).re

/-- `mul_τ = |low_τ|`, `low_τ = {χ ∈ Γ̂ : λ(χ) ≤ τ}` (§2, p.3): the number of characters whose
Laplacian eigenvalue is at most `τ`. -/
noncomputable def mulChar (S : Finset Γ) (τ : ℝ) : ℕ :=
  (univ.filter (fun χ : AddChar Γ ℂ => charLam S χ ≤ τ)).card

/-- The modular distance `|a|_q = min_{k ∈ ℤ} |a − kq|` (§3, p.7). -/
noncomputable def modDist (q a : ℝ) : ℝ :=
  ⨅ k : ℤ, |a - (k : ℝ) * q|

/-- `η_χ(x)`: the unique `j ∈ {0, …, m − 1}` (`m = ord χ`) with `χ(x) = exp(2πij/m)` (3.1).
Every value of a character of order `m` is an `m`-th root of unity, so the `else` branch is never
taken for a character. -/
noncomputable def charEta (χ : AddChar Γ ℂ) (x : Γ) : ℕ :=
  if h : ∃ j : Fin (orderOf χ),
      χ x = Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) : ℂ) / (orderOf χ : ℂ))
  then (Classical.choose h).val else 0

/-- `Sweep(χ) = η_χ^{-1}({0, …, ⌊m/2⌋ − 1})`: the set of `x` with `χ(x) = exp(2πij/m)` for some
natural `j < ⌊m/2⌋`, where `m = ord χ` (§2.1 p.4, §4 p.8; the threshold `t = ⌊m/2⌋ − 1`). -/
noncomputable def sweep (χ : AddChar Γ ℂ) : Finset Γ :=
  univ.filter (fun x => ∃ j : ℕ, j < orderOf χ / 2 ∧
    χ x = Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) / (orderOf χ : ℂ)))

/-- `β(χ) = E_{s∼S}[|η_χ(s)|_m] / m`, `m = ord χ` (§4.2, p.10); `E_{s∼S}` is the uniform average
over `S`. -/
noncomputable def charBeta (S : Finset Γ) (χ : AddChar Γ ℂ) : ℝ :=
  (1 / (S.card : ℝ)) * ∑ s ∈ S,
    modDist (orderOf χ : ℝ) (charEta χ s : ℝ) / (orderOf χ : ℝ)

end AbelianCayleySC.Subexp


