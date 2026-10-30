-- Prove2me | Definitions.Def_HorodeckiBoundKey_finCut
-- name    : HorodeckiBoundKey_finCut
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:33.2245+00:00
-- url     : https://prove2.me/theorems/b70232f6-c4c3-44ae-ae4d-c7697e68142b
-- title:
--   The Alice:Bob cut $AA'{:}BB'$ of a key-and-shield state, on $\mathrm{Fin}\,a\times\mathrm{Fin}\,b$
-- statement:
--   Let $\rho$ be a state on four registers $A, B, A', B'$, where $A$ and $B$ are the key qubits of Alice and Bob and $A'$, $B'$ are their shields (p.2: "Systems $AA'$ ($BB'$) are held by Alice (Bob)"). The state is stored with the key pair first, as a matrix on $(\mathbb C^2\otimes\mathbb C^2)\otimes(A'\otimes B')$. Its **Alice:Bob cut** is the same matrix read as a bipartite operator on
--   $$
--   (A A') \otimes (B B') \;\cong\; \mathbb C^{a}\otimes\mathbb C^{b},\qquad a = 2\,|A'|,\quad b = 2\,|B'| ,
--   $$
--   where each party's register is relabelled by a fixed bijection with $\{0,\dots,a-1\}$ (resp. $\{0,\dots,b-1\}$).
--
--   This adapter is what lets the operational rates of distillable key and distillable entanglement, which are defined for bipartite matrices on $\mathrm{Fin}\,a\times\mathrm{Fin}\,b$, be applied to the key-and-shield states of the paper.
--
--   **Formalization Note** The regrouping is the published `Dependency50.P24.partyCut`; the relabelling uses `Fintype.equivFin` on each side. Every quantity used in the mission (rates, separability, partial transposition) is invariant under local relabellings, so the particular bijection does not matter. The cut loses no information (a proved sanity check).
-- source:
--   Horodecki, Horodecki, Horodecki, Oppenheim, Secure key from bound entanglement, arXiv:quant-ph/0309110v2, p.2 ("Systems AA′ (BB′) are held by Alice (Bob)")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Dependency50.P24 (Key partyCut)

namespace HorodeckiBoundKey

/-- Horodecki, Horodecki, Horodecki, Oppenheim, *Secure key from bound entanglement*,
arXiv:quant-ph/0309110v2, p.2 ("Systems AA′ (BB′) are held by Alice (Bob)"): a state on the
registers `A B A′ B′`, stored as `Op (Key 2 × (S × T))` with `Key 2 = Fin 2 × Fin 2` the key
qubits `(A, B)` and `S × T` the shields `(A′, B′)`, read as a bipartite matrix across the
Alice:Bob cut `AA′ : BB′`, with each party's register relabelled as `Fin a`, `Fin b`.

**Formalization Note.** The register order `Key 2 × (S × T)` is that of the published layer
`Dependency50.P24`; `partyCut` regroups it as `(Fin 2 × S) × (Fin 2 × T)`. The rate
definitions `Gap48.P42.distillableKey` and `bipartiteDistillable` take matrices on
`Fin a × Fin b`, so Alice's register `Fin 2 × S` is relabelled along `Fintype.equivFin`
(`a = card (Fin 2 × S) = 2·|S|`), and Bob's likewise. The relabelling is a fixed local
bijection on each side; every quantity used here (rates, separability, partial transposition)
is invariant under local relabellings, so any fixed choice gives the same statements. -/
noncomputable def finCut {S T : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    (ρ : Op (Key 2 × (S × T))) :
    Matrix (Fin (Fintype.card (Fin 2 × S)) × Fin (Fintype.card (Fin 2 × T)))
      (Fin (Fintype.card (Fin 2 × S)) × Fin (Fintype.card (Fin 2 × T))) ℂ :=
  fun x y => partyCut ρ
    ((Fintype.equivFin (Fin 2 × S)).symm x.1, (Fintype.equivFin (Fin 2 × T)).symm x.2)
    ((Fintype.equivFin (Fin 2 × S)).symm y.1, (Fintype.equivFin (Fin 2 × T)).symm y.2)

end HorodeckiBoundKey


