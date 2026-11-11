-- Prove2me | Definitions.Def_QCollLB_Queries
-- name    : QCollLB_Queries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:12:45.644182+00:00
-- url     : https://prove2.me/theorems/c35896c8-7ce3-4f52-808a-b7c5e19f7bf0
-- title:
--   Definitions 3.2, 5.2, 5.3, Eq. (17) — multiplication operators, genuine forward queries and auxiliary database queries
-- statement:
--   **Multiplication operators.** For $i\in[n]$ and $g:[n]\to\mathbb C$, $M_{i,g}|\pi\rangle=g(\pi(i))|\pi\rangle$ on $P=\mathbb C[S_n]$.
--
--   **Genuine forward queries.** With answer alphabet $\mathbb Z_{n+1}$ (slots $1,\dots,n$, blank $0$), the purified forward query at position $i$ with label $c$ is $O_{i,c}|\pi\rangle=\omega_{n+1}^{c\pi(i)}|\pi\rangle$, i.e. $M_{i,g}$ with $g(u)=\omega_{n+1}^{cu}$. More generally a phase vector $g$ assigns a unit phase to each slot and to the blank.
--
--   **Auxiliary queries.** The local compression $C_i$ is, on each block $D_{i,r}=\mathrm{span}(\{|r\rangle\}\cup\{|r\cup\{i\mapsto z\}\rangle\})$, the reflection exchanging $|r\rangle$ and $|u_{i,r}\rangle=(n-|r|)^{-1/2}\sum_{z\notin\mathrm{Im}\,r}|r\cup\{i\mapsto z\}\rangle$. The database phase is $D_{i,c}|d\rangle=\omega_{n+1}^{c\,d(i)}|d\rangle$ if $i\in\mathrm{Dom}\,d$ and $|d\rangle$ otherwise, and the auxiliary query is
--   $$
--   O_{i,c}=C_i\,D_{i,c}\,C_i\quad\text{on }D .
--   $$
--   Controlled versions $\sum_\ell|\ell\rangle\langle\ell|\otimes O_{i(\ell),g(\ell)}$ act on a control register $\ell\in\Lambda$ together with $P$ or $D$.
--
--   **Formalization Note** $C_i$ is the published `CompPermOracle.compressU`. The 0-based slot $u$ is the paper's slot $u+1$ (`stdPhase`). The control register comes first.
-- source:
--   Peng–Wu, Quantum Lower Bounds for Collision Problems, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Eq. (17) p.20, Definition 3.2 p.19, Definitions 5.2–5.3 p.23

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_SelectiveDPT_phaseOracle

namespace QCollLB

open CompPermOracle

/-- The point-multiplication operator `M_{i,g}|π⟩ = g(π(i))|π⟩` on `P = ℂ[S_n]` (Peng–Wu,
arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Eq. (17), p.20). -/
noncomputable def mulOp {n : ℕ} (i : Fin n) (g : Fin n → ℂ) :
    Hil (Equiv.Perm (Fin n)) →L[ℂ] Hil (Equiv.Perm (Fin n)) :=
  ∑ π : Equiv.Perm (Fin n), g (π i) • ketBra (ket π) (ket π)

/-- The standard phase vector of the answer label `c ∈ Z_{n+1}` (arXiv:2611.01767, Definition 3.2,
p.19, and Definition 5.3, p.23): the blank symbol `0` gets phase `ω_{n+1}^{c·0} = 1` and the slot
`u` gets `ω_{n+1}^{c·u}`.

**Formalization Note.** Slots `1, …, n` are `Fin n` shifted by one: the 0-based slot `u` is the
paper's slot `u + 1`, and `none` is the blank. -/
noncomputable def stdPhase (n : ℕ) (c : ZMod (n + 1)) : Option (Fin n) → ℂ
  | none => 1
  | some u => SelectiveDPT.rootPow (n + 1) (c * (((u : ℕ) + 1 : ℕ) : ZMod (n + 1)))

/-- The genuine forward phase query at position `i` with phase vector `g` on the permutation
register: `|π⟩ ↦ g(π(i))|π⟩` (arXiv:2611.01767, Definition 3.2, p.19: `O_{i,c}|π⟩ = ω_{n+1}^{cπ(i)}|π⟩`,
which is `g = stdPhase n c`; the arbitrary unit phases are those of p.23 and p.37). -/
noncomputable def genQ {n : ℕ} (i : Fin n) (g : Option (Fin n) → ℂ) :
    Hil (Equiv.Perm (Fin n)) →L[ℂ] Hil (Equiv.Perm (Fin n)) :=
  mulOp i fun u => g (some u)

/-- The database phase `D_{i,g}|d⟩ = g(d(i))|d⟩`, with `g(blank)` when `i ∉ Dom d`
(arXiv:2611.01767, Definition 5.3, Eq. (30), p.23: `D_{i,c}` is `g = stdPhase n c`). -/
noncomputable def auxD {n : ℕ} (i : Fin n) (g : Option (Fin n) → ℂ) :
    Hil (PartialPerm n) →L[ℂ] Hil (PartialPerm n) :=
  ∑ d : PartialPerm n, g (d i) • ketBra (ket d) (ket d)

/-- The auxiliary phase query `O_{i,g} = C_i D_{i,g} C_i` on `D` (arXiv:2611.01767,
Definition 5.3, Eq. (31), p.23).

**Formalization Note.** The local compression `C_i` of Definition 5.2, Eq. (29), p.23 (on each block
`D_{i,r}` the reflection exchanging `|r⟩` and `|u_{i,r}⟩ = (n−|r|)^{−1/2} Σ_{z ∉ Im r} |r ∪ {i ↦ z}⟩`)
is the published `CompPermOracle.compressU i`, whose closed form
`I − Σ_{r : i ∉ Dom r} (|r⟩ − |u_{i,r}⟩)(⟨r| − ⟨u_{i,r}|)` is the same operator. -/
noncomputable def auxQ {n : ℕ} (i : Fin n) (g : Option (Fin n) → ℂ) :
    Hil (PartialPerm n) →L[ℂ] Hil (PartialPerm n) :=
  (compressU i).comp ((auxD i g).comp (compressU i))

/-- The controlled genuine query `Σ_ℓ |ℓ⟩⟨ℓ| ⊗ O_{i(ℓ), g(ℓ)}` on `ℂ[Λ] ⊗ P`, for a control
register `Λ` carrying the query position `i(ℓ)` and phase vector `g(ℓ)` (arXiv:2611.01767,
Definition 3.2, p.19: `O = ⨁_{i,c} O_{i,c}`). -/
noncomputable def genCtl {n : ℕ} {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (i : Λ → Fin n)
    (g : Λ → Option (Fin n) → ℂ) :
    Hil (Λ × Equiv.Perm (Fin n)) →L[ℂ] Hil (Λ × Equiv.Perm (Fin n)) :=
  controlled fun l => genQ (i l) (g l)

/-- The controlled auxiliary query `Σ_ℓ |ℓ⟩⟨ℓ| ⊗ O_{i(ℓ), g(ℓ)}` on `ℂ[Λ] ⊗ D`
(arXiv:2611.01767, Definition 5.3, Eq. (31), p.23: `O = ⨁_{i,c} O_{i,c}` on `D ⊗ I ⊗ C_π`).

**Formalization Note.** With `Λ = [n] × Z_{n+1} × W_π`, `i(i,c,w) = i` and `g(i,c,w) = stdPhase n c`
this is the paper's `O ⊗ I_{W_π}`; any other `Λ` is a coherent control of the position and label
together with an ancilla. The control register is written first. -/
noncomputable def auxCtl {n : ℕ} {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (i : Λ → Fin n)
    (g : Λ → Option (Fin n) → ℂ) :
    Hil (Λ × PartialPerm n) →L[ℂ] Hil (Λ × PartialPerm n) :=
  controlled fun l => auxQ (i l) (g l)

end QCollLB


