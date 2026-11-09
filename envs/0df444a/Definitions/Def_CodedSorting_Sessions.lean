-- Prove2me | Definitions.Def_CodedSorting_Sessions
-- name    : CodedSorting_Sessions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:06:57.792745+00:00
-- url     : https://prove2.me/theorems/2ef719ee-6e9f-470b-9ec8-bc9bca80ffc3
-- title:
--   Session labels of a permuting circuit, and the registers of the global circuit
-- statement:
--   For a circuit that recovers input $i$ at output $\sigma(i)$, with labels in $\mathbb Q^m$, the **session label condition** says that for every session $s_i\to t_{\sigma(i)}$:
--
--   1. $U_{t_{\sigma(i)}}=U_{s_i}^\perp$;
--   2. $\dim\big(U_{s_i}+U_{t_{\sigma(i)}}\big)=m$;
--   3. $\operatorname{rank}_{\mathbb Q}\big(M_{t_{\sigma(i)}}-M_{s_i}\big)=m$ for the orthogonal projections $M$ onto these labels.
--
--   The **global registers** are the $W=6v^3+3v^2R$ registers of §5.1 ($v=111$, $R=439$): for each of the three data copies and each grid point $a\in[v]^3$ the pair $X_a,Y_a$, and for each $i\in\{1,2,3\}$ and $b,c\in[v]$ the $R$ registers of the shared auxiliary pool $P_i(b,c)$. The **global exchange** swaps $X_a$ and $Y_a$ in every copy and fixes every auxiliary register.
--
--   Condition 1 holds for the paper's circuit: $X_a$ goes from $U_a$ to $U_a^\perp$, and $Y_a$ and every auxiliary register go from $0$ to $H$ (proof of Lemma 5.3); it is what Lemma 6.2 uses to make the source and sink partial swaps compose to the full interchange.
-- source:
--   B. Li, Z. Li, S. Liu, Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), §5.1, pp.13–15 (PDF 14–16), and Lemma 5.3, (9), p.16 (PDF 17)

import Mathlib
import Definitions.Def_CodedSorting_Circuit
import Definitions.Def_CodedSorting_LinAlg

namespace CodedSorting

/-! # Sessions, source/sink labels, and the registers of the global circuit

arXiv:2610.20079 (held version, sha256 6e149d97…8850b), §5.1, pp.13–15, and Lemma 5.3, p.16. -/

/-- **Source/sink labels of the sessions** (Lemma 5.3, (9), p.16). For a circuit recovering input
`i` at output `σ i`, with node labels in `ℚ^m`: for every session `s_i → t_{σ(i)}`,
1. the sink label is the orthogonal complement of the source label (`U_t = U_s^⊥`: `U_a` and
   `U_a^⊥` for `X_a → Y_a`, `0` and `H` otherwise, proof of Lemma 5.3, p.16);
2. `dim(U_{s_i} + U_{t_{σ(i)}}) = m`;
3. `rank_ℚ(M_{t_{σ(i)}} − M_{s_i}) = m` for the orthogonal projections `M` onto these labels. -/
def SessionLabels {ι κ : Type} {m : ℕ} (C : XorCircuit ι κ) (σ : ι → ι)
    (lab : Node ι C.G → Submodule ℚ (Fin m → ℚ)) : Prop :=
  ∀ i, lab (.sink (σ i)) = perp (lab (.source i)) ∧
    Module.finrank ℚ ↥(lab (.source i) ⊔ lab (.sink (σ i))) = m ∧
    ∀ P Q : Matrix (Fin m) (Fin m) ℚ, IsOrthProj (lab (.source i)) P →
      IsOrthProj (lab (.sink (σ i))) Q → (Q - P).rank = m

/-- The `W = 6v³ + 3v²R` registers of the global circuit (§5.1, pp.13–15), `v = 111`, `R = 439`:
* `inl (c, a, b)`: in data copy `c ∈ {1, 2, 3}` (`Fin 3`), at grid point `a = (a₁, a₂, a₃) ∈ [v]³`,
  register `X_a` (`b = false`) or `Y_a` (`b = true`);
* `inr (i, (b, c), r)`: register `r ∈ [R]` of the shared auxiliary pool `P_i(b, c)`,
  `i ∈ {1, 2, 3}`, `b, c ∈ [v]`. -/
abbrev GlobalReg :=
  (Fin 3 × (Fin 111 × Fin 111 × Fin 111) × Bool) ⊕ (Fin 3 × (Fin 111 × Fin 111) × Fin 439)

/-- The exchange of every data pair: `X_a ↔ Y_a` in each copy; auxiliary registers fixed. -/
def globalSwap : GlobalReg → GlobalReg
  | .inl (c, a, b) => .inl (c, a, !b)
  | .inr p => .inr p

end CodedSorting


