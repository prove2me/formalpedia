-- Prove2me | Definitions.Def_ProofCryptoSynergy_Supplement_WRel
-- name    : ProofCryptoSynergy_Supplement_WRel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:44:46.324251+00:00
-- url     : https://prove2.me/theorems/894e0ad5-0dd1-464a-9d7e-a4d5a8af253a
-- title:
--   Promise problems given by witness relations; SAT; many-one, witness mapping and witness recovery
-- statement:
--   A **promise problem given by witness relations** $(R_Y,R_N)$ has yes-instances $Y=\{z:\exists w\ (z,w)\in R_Y\}$ and no-instances $N=\{z:\forall w\ (z,w)\notin R_N\}$ (Definition 3). Instances and witnesses are typed.
--
--   **SAT** is the promise problem with $R_Y=R_N=\{(\varphi,w):\varphi(w)=1,\ |w|\le|\varphi|\}$, so $Y$ is the set of satisfiable formulas and $N$ the set of unsatisfiable ones.
--
--   For promise problems $(R^1_Y,R^1_N)$ and $(R^2_Y,R^2_N)$ and maps $f,g,h$ (Definition 4):
--   1. $f$ is **many-one** if $x\in Y_1\Rightarrow f(x)\in Y_2$ and $x\in N_1\Rightarrow f(x)\in N_2$;
--   2. $g$ **maps witnesses** if $(x,w)\in R^1_Y\Rightarrow (f(x),g(x,w))\in R^2_Y$;
--   3. $h$ **recovers witnesses** if $(f(x),w)\in R^2_N\Rightarrow (x,h(x,w))\in R^1_N$.
--
--   These are the conditions of the paper's Levin and half-Levin reductions.
--
--   **Formalization Note** Definition 3's inclusion $R_Y\subseteq R_N$ is not imposed as a field: the learning problems are used exactly as defined. $\varphi(w)=1$ is the published `holds`; every variable of a formula has index below $|\varphi|$, so bounding $|w|\le|\varphi|$ changes neither $Y$ nor $N$.
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 3, p.16 (PDF 18); Definition 4, p.17 (PDF 19)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_TAUT

namespace ProofCryptoSynergy.Supplement

/-- A **promise problem given by witness relations** `(R_Y, R_N)` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 3, p.16
(PDF 18)): the yes-instances are `Y = {z | ∃ w, (z, w) ∈ R_Y}` and the no-instances are
`N = {z | ∀ w, (z, w) ∉ R_N}`.

**Formalization Note** Instances and witnesses are typed (`I`, `W`): formulas and assignments for
SAT, sampling circuits and circuits for the learning problems. Definition 3's inclusion
`R_Y ⊆ R_N` is not a field: it is a property of each concrete problem, and the theorems use the
relations exactly as Definitions 21–27 and 73 print them. -/
structure WRel (I W : Type) where
  /-- the yes-relation `R_Y` -/
  RY : I → W → Prop
  /-- the "not-no" relation `R_N` -/
  RN : I → W → Prop

/-- The yes-instances `Y = {z | ∃ w, (z, w) ∈ R_Y}`. -/
def WRel.Yes {I W : Type} (P : WRel I W) : Set I := {z | ∃ w, P.RY z w}

/-- The no-instances `N = {z | ∀ w, (z, w) ∉ R_N}`. -/
def WRel.No {I W : Type} (P : WRel I W) : Set I := {z | ∀ w, ¬ P.RN z w}

/-- **SAT as a promise problem** with `R_Y = R_N = {(φ, w) : φ(w) = 1, |w| ≤ |φ|}`
(Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), §2.2, p.18 (PDF 20); Definition 3, p.16).

**Formalization Note** `φ(w) = 1` is the published `holds`. Every variable of the formula a
string `φ` reads as has index below `|φ|`, so a satisfying assignment can always be cut to length
`|φ|`: `Y` is the set of satisfiable formulas and `N` the set of unsatisfiable ones. -/
def SATRel : WRel (List Bool) (List Bool) where
  RY φ w := holds φ w ∧ w.length ≤ φ.length
  RN φ w := holds φ w ∧ w.length ≤ φ.length

/-- Condition 1 of Definition 4 (many-one): `x ∈ Y₁ → f(x) ∈ Y₂` and `x ∈ N₁ → f(x) ∈ N₂`
(Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 4, p.17 (PDF 19)). -/
def ManyOne {I₁ W₁ I₂ W₂ : Type} (P₁ : WRel I₁ W₁) (P₂ : WRel I₂ W₂) (f : I₁ → I₂) : Prop :=
  (∀ x ∈ P₁.Yes, f x ∈ P₂.Yes) ∧ (∀ x ∈ P₁.No, f x ∈ P₂.No)

/-- Condition 2 of Definition 4 (witness mapping): `(x, w) ∈ R₁_Y → (f(x), g(x, w)) ∈ R₂_Y`
(Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 4, p.17 (PDF 19)). -/
def WitnessMap {I₁ W₁ I₂ W₂ : Type} (P₁ : WRel I₁ W₁) (P₂ : WRel I₂ W₂) (f : I₁ → I₂)
    (g : I₁ → W₁ → W₂) : Prop :=
  ∀ x w, P₁.RY x w → P₂.RY (f x) (g x w)

/-- Condition 3 of Definition 4 (witness recovery): `(f(x), w) ∈ R₂_N → (x, h(x, w)) ∈ R₁_N`
(Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 4, p.17 (PDF 19)). -/
def WitnessRecover {I₁ W₁ I₂ W₂ : Type} (P₁ : WRel I₁ W₁) (P₂ : WRel I₂ W₂) (f : I₁ → I₂)
    (h : I₁ → W₂ → W₁) : Prop :=
  ∀ x w, P₂.RN (f x) w → P₁.RN x (h x w)

end ProofCryptoSynergy.Supplement


