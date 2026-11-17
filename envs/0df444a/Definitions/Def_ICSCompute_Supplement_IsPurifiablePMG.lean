-- Prove2me | Definitions.Def_ICSCompute_Supplement_IsPurifiablePMG
-- name    : ICSCompute_Supplement_IsPurifiablePMG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T15:02:47.301491+00:00
-- url     : https://prove2.me/theorems/f658e588-2b48-4a0b-bc50-3fb5101cf9de
-- title:
--   Purifiable process matrices and purifiable PMGs
-- statement:
--   Let $W$ be a process matrix (Definition 4.4) with $n$ single-qubit feedback pairs, feedback input $R=S(n)$, feedback output $S=S(n)$, external input $P$ and external output $F$. Then $W$ is **purifiable** if there are additional external qubit registers $P'=S(p')$, $F'=S(f')$ and a unitary
--   $$U:\ H_R\otimes H_P\otimes H_{P'}\to H_S\otimes H_F\otimes H_{F'}$$
--   such that
--   1. $\widetilde W:=|U\rangle\rangle\langle\langle U|$, where $|M\rangle\rangle=\sum_x|x\rangle\otimes M|x\rangle$, is a process matrix for the same feedback pairs with external input $(P,P')$ and external output $(F,F')$;
--   2. initializing $P'$ to $|0\rangle$ and discarding $F'$ recovers $W$: with $V:=U(I_{H_R\otimes H_P}\otimes|0\rangle_{P'})$,
--   $$W=\operatorname{Tr}_{F'}\big(|V\rangle\rangle\langle\langle V|\big).$$
--
--   A circuit description $D=(n,C)$ is a **purifiable PMG** if $\mathrm{CJ}(\mathcal C_C)$ is a purifiable process matrix for its $n$ feedback pairs (Definition 4.10). Purifiability, proposed by Araújo, Feix, Navascués and Brukner as a physicality condition, is the extra condition on valid generation queries in Theorem 1.1.
--
--   **Formalization Note** The extension $U$ is a unitary matrix, not a circuit: no circuit for $U$, size bound or constructibility is required, as the paper states after Definition 4.10. Registers are indexed input first, $((R,P),(S,F))$, as in the mission's published process-matrix layer. The predicate contains the standing hypothesis that $W$ itself is a process matrix, so a purifiable PMG is in particular a PMG.
-- source:
--   Shmueli, What Can Be Computed with Indefinite Causal Structure?, arXiv:2610.40573 (version of 2026-11-03, sha256 d3e36399…b606), Definitions 4.9 and 4.10, pp.21–22 (PDF pp.23–24); Definition 4.1, p.18

import Mathlib
import Definitions.Def_ICSCompute_IsProcessMatrix
import Definitions.Def_ICSCompute_IsPurePMG

namespace ICSCompute.Supplement

open QAlgorithms

/-- The operator `|U⟩⟩⟨⟨U|` of a matrix `U ∈ L(H_α, H_β)` (Shmueli, arXiv:2610.40573,
Definition 4.1, p.18 (PDF p.20): `|M⟩⟩ := ∑_x |x⟩ ⊗ M|x⟩`), indexed input first: its
`((a, b), (a', b'))` entry is `U_{b a} · conj(U_{b' a'})`. For `U` unitary this is the Choi
operator `CJ(Ad U)` of Definition 3.14. -/
def choiOp {α β : Type*} (U : Matrix β α ℂ) : Matrix (α × β) (α × β) ℂ :=
  Matrix.of fun a b => U a.2 a.1 * star (U b.2 b.1)

/-- **Purifiable process matrix** (Shmueli, *What Can Be Computed with Indefinite Causal
Structure?*, arXiv:2610.40573, version of 2026-11-03, sha256 d3e36399…b606, Definition 4.9,
p.21 (PDF p.23)). A process matrix `W` with feedback input `R`, feedback output `S`, external
input `P` and external output `F` is purifiable if there are additional external registers
`P′`, `F′` and a unitary `U : H_R ⊗ H_P ⊗ H_{P′} → H_S ⊗ H_F ⊗ H_{F′}` such that
1. `W̃ := |U⟩⟩⟨⟨U|` is a process matrix for the same feedback pairs, with external input
   `P, P′` and external output `F, F′`;
2. with `V := U (I_{H_R ⊗ H_P} ⊗ |0⟩_{P′})`, `W = Tr_{F′}(|V⟩⟩⟨⟨V|)`.

**Formalization Note** `n` separate single-qubit feedback pairs, `R = S(n)` (`AI`) and
`S = S(n)` (`AO`), with the base mission's input-first indexing `((R, P), (S, F))`. `P′ = S(p′)`
and `F′ = S(f′)` are qubit registers of arbitrary size (zero allowed). `U` is a matrix from
`R × (P × P′)` to `S × (F × F′)` with `U†U = I` and `UU† = I` (so the dimensions agree); no
circuit for `U`, no size bound and no constructibility is required (p.22). Condition 2 is written
entrywise: `W((x, p), (s, f)), ((x′, p″), (s′, f″)) = ∑_g V((s, (f, g)), (x, p)) ·
conj V((s′, (f″, g)), (x′, p″))` with `V((s, (f, g)), (x, p)) = U((s, (f, g)), (x, (p, 0)))`.
The clause `IsProcessMatrix W` records the definition's standing hypothesis "Let `W` be a
process matrix". -/
def IsPurifiable {n : ℕ} {P F : Type*} [Fintype P] [DecidableEq P] [Fintype F] [DecidableEq F]
    (W : Matrix ((Qubits n × P) × (Qubits n × F)) ((Qubits n × P) × (Qubits n × F)) ℂ) :
    Prop :=
  IsProcessMatrix W ∧
    ∃ (p' f' : ℕ) (U : Matrix (Qubits n × (F × Qubits f')) (Qubits n × (P × Qubits p')) ℂ),
      U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1 ∧
      IsProcessMatrix (n := n) (P := P × Qubits p') (F := F × Qubits f') (choiOp U) ∧
      ∀ a b, W a b = ∑ g : Qubits f',
        U (a.2.1, (a.2.2, g)) (a.1.1, (a.1.2, fun _ => false)) *
          star (U (b.2.1, (b.2.2, g)) (b.1.1, (b.1.2, fun _ => false)))

/-- **Purifiable process matrix generator** (Shmueli, *What Can Be Computed with Indefinite
Causal Structure?*, arXiv:2610.40573, version of 2026-11-03, sha256 d3e36399…b606,
Definition 4.10, p.22 (PDF p.24)): "Let `D = (n, C)` be a PMG as in Definition 4.5. We say that
`D` is purifiable if `CJ(𝒞_C)` is a purifiable process matrix according to Definition 4.9, with
the same `n` separate single-qubit feedback pairs."

**Formalization Note** `IsPurifiable` contains `IsProcessMatrix (choiW D)`, which is `IsPMG D`,
so the PMG hypothesis of the definition is part of this predicate. The circuit `C` may discard
wires; purifiability asks for a unitary matrix, not a unitary circuit (p.22: "The existence of
such a circuit over our fixed gate set, its size, and the complexity of constructing it are
additional requirements, not part of purifiability"). -/
def IsPurifiablePMG {n r ℓ : ℕ} (D : Desc n r ℓ) : Prop :=
  IsPurifiable (choiW D)

end ICSCompute.Supplement


