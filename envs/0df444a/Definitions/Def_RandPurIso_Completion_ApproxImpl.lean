-- Prove2me | Definitions.Def_RandPurIso_Completion_ApproxImpl
-- name    : RandPurIso_Completion_ApproxImpl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:30:20.583192+00:00
-- url     : https://prove2.me/theorems/f162b9a3-0856-4e4e-9af8-4f386a77eb46
-- title:
--   Implementation within trace distance $\varepsilon$ with at most $B$ gates
-- statement:
--   `ApproxImpl e K ε B` says: there is a Clifford+T circuit with at most $B$ gates on the encoded register (encoding $e$ plus a flag qubit for $\perp$) and some ancillas, whose channel is within trace distance $\varepsilon$ of $\Phi_K$ on every density matrix of $X\otimes R$, for every finite reference register $R$, both channels acting with the identity on $R$. This is Lemma 3.15's "can be implemented to within trace-distance error $\epsilon$, including an arbitrary reference register, using … gates".
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Lemma 3.15, p. 24

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_RandPurIso_Completion_circChannel
import Definitions.Def_RandPurIso_Completion_contractionChannel
import Definitions.Def_RandPurIso_Completion_traceDist
open Matrix

namespace RandPurIso.Completion

open ShiShallow

/-- Append a flag qubit (set to `0`) to an encoding; strings with the flag set read as `⊥`. -/
def withFlag {X : Type} {m : ℕ} (e : X → Bits m) (x : X) : Bits (m + 1) :=
  Fin.append (e x) (fun _ => false)

/-- No oracles (gate-only circuits). -/
def noOracleW : Fin 0 → ℕ := fun j => j.elim0

/-- The empty oracle family. -/
def noOracle : (j : Fin 0) → Matrix (Bits (noOracleW j)) (Bits (noOracleW j)) ℂ →
    Matrix (Bits (noOracleW j)) (Bits (noOracleW j)) ℂ := fun j => j.elim0

/-- **"The channel associated with `K` can be implemented to within trace-distance error `ε`,
including an arbitrary reference register, using at most `B` gates"** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Lemma 3.15, p. 24).

There is a Clifford+T circuit on the encoded register (`e`, plus a flag qubit for `⊥`) and `a`
ancillas, with at most `B` gates, whose channel (`circChannel`) is within trace distance `ε` of
`Φ_K` (`contractionChannel`) on every density matrix of `X ⊗ R`, for every finite reference
register `R = Fin r`, both channels acting with the identity on `R`. -/
def ApproxImpl {X : Type} [Fintype X] [DecidableEq X] {m : ℕ} (e : X → Bits m)
    (K : Matrix X X ℂ) (ε B : ℝ) : Prop :=
  ∃ (a : ℕ) (c : List (QInstr 0 noOracleW (m + 1 + a))), (c.length : ℝ) ≤ B ∧
    ∀ (r : ℕ) (ρ : Matrix (X × Fin r) (X × Fin r) ℂ), PeresTerno.IsDensityMatrix ρ →
      traceDist (PeresTerno.ampliate (circChannel c noOracle (withFlag e) (withFlag e)) ρ)
        (PeresTerno.ampliate (contractionChannel K) ρ) ≤ ε

end RandPurIso.Completion


