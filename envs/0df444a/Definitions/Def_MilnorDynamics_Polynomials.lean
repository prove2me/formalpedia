-- Prove2me | Definitions.Def_MilnorDynamics_Polynomials
-- name    : MilnorDynamics_Polynomials
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-26T10:40:09.965216+00:00
-- url     : https://prove2.me/theorems/708a93b2-805f-4f16-9480-dc94ca8e0af9
-- title:
--   Polynomials as maps of the sphere; filled Julia set, Julia and Fatou sets of a polynomial (Milnor §9)
-- statement:
--   Polynomial-specific objects of Milnor's §9 (*Böttcher's Theorem and Polynomial Dynamics*).
--
--   1. A complex polynomial $P$ is regarded as the rational map $P/1$ of the Riemann sphere $\hat{\mathbb C}$; it fixes $\infty$.
--   2. The **filled Julia set** of $P$ is
--   $$
--   K(P)=\{z\in\mathbb C : \text{the orbit } z,P(z),P(P(z)),\dots \text{ is bounded}\}.
--   $$
--   3. The **Julia set** $J(P)\subseteq\mathbb C$ and the **Fatou set** $\mathbb C\setminus J(P)$ are the finite parts of the Julia and Fatou sets of $P$ as a map of the sphere (the point $\infty$ always lies in the Fatou set of a polynomial of degree $\ge2$).
--
--   **Formalization Note** The Julia and Fatou sets are those of the second mission of this series, pulled back along the inclusion $\mathbb C\hookrightarrow\hat{\mathbb C}$. Boundedness is Mathlib's `Bornology.IsBounded`.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, §9, p. 95 (definition of the filled Julia set K(f)); §4 p. 40 (Fatou and Julia sets)

import Mathlib
import Definitions.Def_MilnorDynamics_RationalMaps

open scoped OnePoint
open Filter Set Polynomial

namespace MilnorDynamics

/-- A complex polynomial `P`, viewed as the rational map `P/1` of the Riemann sphere. -/
noncomputable def polyToRationalMap (P : ℂ[X]) : RationalMap :=
  ⟨P, 1, one_ne_zero, isCoprime_one_right⟩

/-- The filled Julia set `K(P)` of a polynomial: the points of `ℂ` with bounded forward orbit. -/
def filledJuliaSet (P : ℂ[X]) : Set ℂ :=
  {z | Bornology.IsBounded (Set.range fun n : ℕ => (fun w => P.eval w)^[n] z)}

/-- The Julia set `J(P) ⊆ ℂ` of a polynomial: the finite points of the Julia set of `P`
viewed as a rational map of the Riemann sphere. -/
def polyJuliaSet (P : ℂ[X]) : Set ℂ :=
  (fun z : ℂ => (z : OnePoint ℂ)) ⁻¹' juliaSet (polyToRationalMap P).toFun

/-- The finite Fatou set `ℂ ∖ J(P)` of a polynomial. -/
def polyFatouSet (P : ℂ[X]) : Set ℂ :=
  (fun z : ℂ => (z : OnePoint ℂ)) ⁻¹' fatouSet (polyToRationalMap P).toFun

end MilnorDynamics


