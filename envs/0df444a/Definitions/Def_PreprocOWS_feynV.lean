-- Prove2me | Definitions.Def_PreprocOWS_feynV
-- name    : PreprocOWS_feynV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:22:41.211192+00:00
-- url     : https://prove2.me/theorems/b6d65b90-6987-466a-8702-0790afd3bb99
-- title:
--   Query projectors $Q_{a,y}$ and the Feynman-path vectors $|v_{t,S,x}\rangle$
-- statement:
--   For an algorithm with query map $q$, $Q_o$ is the projector onto the basis states $s$ with $q(s)=o$ (the page's $Q_{a,y}=|a,y\rangle\langle a,y|\otimes I$). For a start state $\psi$ on (advice)$\otimes$(database) define, for databases $S$ and challenges $x\in[N]$,
--   $$
--   |v_{0,S,x}\rangle=\alpha_S|x\rangle|\varphi_S\rangle,\qquad |v_{t,S,x}\rangle=\sum_{o}Q_{o}\,U_t\,|v_{t-1,S\oplus o,x}\rangle\quad(1\le t\le T),
--   $$
--   where $\alpha_S|\varphi_S\rangle$ is the vector $z\mapsto\psi(z,S)$, placed at challenge $x$ with workspace $|0^w\rangle$, and $o$ runs over all query values.
--
--   These vectors split the final state of the game by the database, path by path; displays (8)–(11) are statements about them.
--
--   **Formalization Note** $S\oplus\bot=S$; the value at $t>T$ is $0$ and never used.
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), §5.3, Feynman path formulation, p.20 (PDF p.23)

import Mathlib
import Definitions.Def_PreprocOWS_Alg
import Definitions.Def_PreprocOWS_DB
open Matrix

namespace PreprocOWS

/-- The query projector `Q_o = |o⟩⟨o| ⊗ I`: the projector onto the basis states `s` whose query is
`q(s) = o` (arXiv:2610.02101, §5.3, p.20, PDF p.23: "Write Q_{a,y} := |a,y⟩⟨a,y| ⊗ I"). -/
def Qproj {S T K N w : ℕ} (A : Alg S T K N w) (o : Option (Fin K × Fin N)) :
    Matrix (Ω S N w) (Ω S N w) ℂ :=
  Matrix.diagonal fun s => if A.q s = o then 1 else 0

/-- The **Feynman-path vectors** `|v_{t,S,x}⟩`, Dong–Lombardi, arXiv:2610.02101 (version of 2026-11-02,
sha256 7a0bd8da…), §5.3, Feynman path formulation, p.20 (PDF p.23), for a database state `ψ`:
`|v_{0,S,x}⟩ = α_S |x⟩|φ_S⟩` (here the vector `z ↦ ψ(z,S)` placed at challenge `x`, workspace
`|0^w⟩`), and `|v_{t,S,x}⟩ = ∑_{(a,y)} Q_{a,y} U_t |v_{t−1, S ⊕ (a,y), x}⟩`.

**Formalization Note.** The sum runs over all query values `o ∈ Option ([K]×[N])`, with
`S ⊕ none = S`; `U_t` is `A.U ⟨t−1, _⟩`. The value at `t > T` is `0` and is never used. -/
noncomputable def feynV {S T K N w : ℕ} (A : Alg S T K N w) (ψ : Fin (2 ^ S) × DB K N → ℂ) :
    ℕ → DB K N → Fin N → Ω S N w → ℂ
  | 0, D, x => fun s => if s.2.1 = x ∧ s.2.2 = wsZero w then ψ (s.1, D) else 0
  | t + 1, D, x =>
    if h : t < T then
      ∑ o : Option (Fin K × Fin N),
        (Qproj A o * (A.U ⟨t, h⟩ : Matrix (Ω S N w) (Ω S N w) ℂ)) *ᵥ feynV A ψ t (togOpt o D) x
    else 0

end PreprocOWS


