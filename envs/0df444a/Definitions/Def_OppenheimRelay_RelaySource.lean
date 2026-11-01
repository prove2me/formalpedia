-- Prove2me | Definitions.Def_OppenheimRelay_RelaySource
-- name    : OppenheimRelay_RelaySource
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:26:22.855995+00:00
-- url     : https://prove2.me/theorems/f17eacde-f9fb-4a36-8465-750007f49e7a
-- title:
--   The relay source: registers $R, A, C, B$ of one copy
-- statement:
--   One copy of the source of the coherent relay has four registers, held by four parties:
--
--   1. $A$, Alice's share, the part that must be transferred;
--   2. $C$, Charlie's share, the side information of the relay station;
--   3. $B$, Bob's share, the receiver's side information;
--   4. $R$, an inaccessible reference system purifying $\rho_{ABC}$, so that the total state $|\psi\rangle_{ABCR}$ is pure.
--
--   The joint basis of one copy is $R\times(A\times(C\times B))$.
--
--   Every statement of the mission is about a unit vector $\psi$ on this space: an arbitrary mixed $\rho_{ABC}$ enters through any of its purifications, as in the paper ("One imagines a total pure state $|\psi\rangle_{ABCR}$ by introducing a reference system $R$").
--
--   **Formalization Note** The order $R, A, C, B$ is the order of the published Devetak–Yard layer (`RedistributionSource`), but the letters carry this paper's roles: there the transferred register is called $C$ and the kept one $A$.
-- source:
--   Oppenheim, State redistribution as merging: introducing the coherent relay, arXiv:0805.1065v1, p.1, paragraph "In state redistribution…", and p.2, "Alice is split into two parties"

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20

namespace OppenheimRelay

/-- **The relay source.** Oppenheim, *State redistribution as merging: introducing the coherent relay*, arXiv:0805.1065v1, p.1, paragraph "In state redistribution…"
("One imagines a total pure state |ψ⟩ABCR by introducing a reference system R") and p.2
("Alice is split into two parties"): the four registers of one copy, in the order R, A, C, B.
A is Alice's share (the part that is sent), C is Charlie's share (the relay's side information),
B is Bob's share, R is the inaccessible reference.

**Formalization Note** This is the same type as the published `RedistributionSource A C B R`, but
the letters have the paper's roles here: `RedistributionSource` calls the sent register `C` and
the kept one `A`. -/
abbrev RelaySource (A C B R : Type*) := R × (A × (C × B))

end OppenheimRelay


