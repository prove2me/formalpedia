-- Prove2me | Definitions.Def_MayersBC_cheatAccept
-- name    : MayersBC_cheatAccept
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:56:14.538751+00:00
-- url     : https://prove2.me/theorems/8b40b9f2-329c-483e-b46b-5838c7c95f28
-- title:
--   Acceptance probability of a delayed-measurement opening
-- statement:
--   A dishonest Alice prepares her system $A$ together with the photons in one pure state $\varphi$, sends the photons, and only at opening time measures $A$ with a POVM $\{N_w\}$, announcing the outcome $w$ as her opening. Bob measures the photons with $\{E_y\}$. The probability that Bob accepts the opening of $b$ is
--
--   $$
--   \sum_{w} \sum_{y:\ T_b(w,y)} \langle \varphi |\, N_w \otimes E_y \,| \varphi\rangle .
--   $$
--
--   The two measurements act on different systems and commute, so the joint distribution of $(w, y)$ does not depend on who measures first. This is the paper's $\Pr(T_1(Y) = ok \mid \Phi = \varphi)$.
--
--   **Formalization Note** Alice's system is the first tensor factor; the test is decided classically.
-- source:
--   Mayers, The Trouble with Quantum Bit Commitment, arXiv:quant-ph/9603015v3, section b, p.5; section d, p.9

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
open QAlgorithms

namespace MayersBC

open Classical in
/-- Mayers, arXiv:quant-ph/9603015v3, section b, p.5 and section d, p.9: the probability that Bob
accepts a claimed opening of `b` when Alice has prepared the joint system (her system `A` and
the photons) in the pure state `φ`, measures `A` with the POVM `N` to obtain the claim `w`, and
Bob measures the photons with the POVM `E` to obtain `y`:
`Σ_w Σ_y [T_b(w, y)] ⟨φ| N_w ⊗ E_y |φ⟩` (the page's `Pr(T_1(Y) = ok | Φ = φ)`).

**Formalization Note.** "These two measurements commute" (p.5), so the joint outcome law is
`⟨φ|N_w ⊗ E_y|φ⟩` whatever the order. Alice's register is the **first** tensor factor
(`A × ι`, `Matrix.kronecker (N w) (E y)`), matching `QAlgorithms.traceLeft`. The test is any
predicate, decided classically. -/
noncomputable def cheatAccept {A W Y ι : Type} [Fintype A] [Fintype W] [Fintype Y] [Fintype ι]
    (φ : EuclideanSpace ℂ (A × ι)) (N : W → Matrix A A ℂ) (E : Y → Matrix ι ι ℂ)
    (T : ZMod 2 → W → Y → Prop) (b : ZMod 2) : ℝ :=
  ∑ w, ∑ y, if T b w y then effectProb (Matrix.kronecker (N w) (E y)) (pureDensity φ) else 0

end MayersBC


