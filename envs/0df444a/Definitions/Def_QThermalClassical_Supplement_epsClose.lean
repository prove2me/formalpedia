-- Prove2me | Definitions.Def_QThermalClassical_Supplement_epsClose
-- name    : QThermalClassical_Supplement_epsClose
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:37:47.867409+00:00
-- url     : https://prove2.me/theorems/087ec92a-404b-4eaa-a408-215b147c2f44
-- title:
--   Decompositions $H=H_0+V$, $w_{\mathrm{free}}$, $w_{\mathrm{pert}}$ and $\epsilon$-closeness to commuting
-- statement:
--   A **decomposition** (32) of a Pauli Hamiltonian is $H=H_0+V$ with $H_0=\sum_\sigma u_\sigma P_\sigma$ (pairwise commuting Paulis) and $V=\sum_\mu v_\mu Q_\mu$ (arbitrary Paulis). Two Pauli strings are **compatible** (33), $W_1\sim W_2$, if $\{W_1,W_2\}=0$ or some $P_\sigma$ anticommutes with both. The **anticommutation parameters** (34) are
--   $$
--   w_{\mathrm{free}}=\max_{\mu}\sum_{\sigma:\{P_\sigma,Q_\mu\}=0}|u_\sigma|,\qquad
--   w_{\mathrm{pert}}=\max_{\mu}\Big(|v_\mu|+\sum_{\nu\neq\mu:\ \nu\sim\mu}|v_\nu|\Big),
--   $$
--   and (Definition 2.6) $H$ is **$\epsilon$-close to commuting** if
--   $$
--   \epsilon(H)=\inf_{H=H_0+V}\frac{w_{\mathrm{pert}}}{w_{\mathrm{free}}+w_{\mathrm{pert}}}\le\epsilon,
--   $$
--   with the value $0$ for a decomposition with $V=0$.
--
--   **Formalization Note** $H_0$ and $V$ are coefficient functions $u,v$ with $\mathrm{ham}\,u+\mathrm{ham}\,v=H$ and no identity term; the maxima are over the terms of $V$ ($0$ if there are none). The infimum is a real infimum over all decompositions of the operator; it need not be attained.
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), §2.4, eqs. (32)–(35), Definition 2.6, p.16

import Mathlib
import Definitions.Def_QThermalClassical_ham
import Definitions.Def_QThermalClassical_IsCommutingPauli

set_option autoImplicit false

namespace QThermalClassical.Supplement

/-- Two Pauli words anticommute: `{W₁, W₂} = W₁W₂ + W₂W₁ = 0`. -/
def PauliAnticommute {Q : Type} [Fintype Q] [DecidableEq Q] (W₁ W₂ : PauliWord Q) : Prop :=
  pauliOp W₁ * pauliOp W₂ + pauliOp W₂ * pauliOp W₁ = 0

/-- A decomposition `H = H₀ + V` of eq. (32) of the Pauli Hamiltonian `ham c`: `H₀ = Σ_σ u_σ P_σ`
with pairwise commuting Pauli strings and `V = Σ_μ v_μ Q_μ` arbitrary, as two coefficient
functions `u, v` with `ham u + ham v = ham c`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), §2.4, eq. (32), p.16.

**Formalization Note.** The terms of `H₀` and `V` are the words with nonzero coefficient;
neither part has an identity term (the Paulis of (5) are non-identity; an identity term affects
neither (33) nor the infimum (35)). The decomposition is of the operator `ham c`, not of the
coefficient list, so a word may appear in both parts. -/
def IsDecomposition {Q : Type} [Fintype Q] [DecidableEq Q] (c u v : PauliWord Q → ℝ) : Prop :=
  u (fun _ => 0) = 0 ∧ v (fun _ => 0) = 0 ∧ ham u + ham v = ham c ∧ IsCommutingPauli u

/-- The compatibility relation (33) for the decomposition with commuting part `u`:
`W₁ ∼ W₂` iff `{W₁, W₂} = 0` or some term `P_σ` of `H₀` anticommutes with both. -/
def PauliCompatible {Q : Type} [Fintype Q] [DecidableEq Q] (u : PauliWord Q → ℝ) (W₁ W₂ : PauliWord Q) : Prop :=
  PauliAnticommute W₁ W₂ ∨ ∃ σ, u σ ≠ 0 ∧ PauliAnticommute W₁ σ ∧ PauliAnticommute W₂ σ

open Classical in
/-- `w_free = max_{μ∈G} Σ_{σ∈F : {P_σ, Q_μ} = 0} |u_σ|` of eq. (34) (`0` when `V = 0`).

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), eq. (34), p.16. -/
noncomputable def wFree {Q : Type} [Fintype Q] [DecidableEq Q] (u v : PauliWord Q → ℝ) : ℝ :=
  ⨆ μ : {μ : PauliWord Q // v μ ≠ 0},
    ∑ σ ∈ Finset.univ.filter (fun σ => u σ ≠ 0 ∧ PauliAnticommute σ μ.1), |u σ|

open Classical in
/-- `w_pert = max_{μ∈G} (|v_μ| + Σ_{ν∈G∖{μ} : ν∼μ} |v_ν|)` of eq. (34) (`0` when `V = 0`).

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), eq. (34), p.16. -/
noncomputable def wPert {Q : Type} [Fintype Q] [DecidableEq Q] (u v : PauliWord Q → ℝ) : ℝ :=
  ⨆ μ : {μ : PauliWord Q // v μ ≠ 0},
    (|v μ.1| + ∑ ν ∈ Finset.univ.filter (fun ν => ν ≠ μ.1 ∧ v ν ≠ 0 ∧ PauliCompatible u ν μ.1),
      |v ν|)

/-- `ε(H) = inf_{H = H₀ + V} w_pert / (w_free + w_pert)` of Definition 2.6, eq. (35), with the
value `0` for a decomposition with `V = 0`. `H` is `ε`-close to commuting iff `ε(H) ≤ ε`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Definition 2.6, eq. (35), p.16.

**Formalization Note.** The real `sInf`; the set is nonempty (`u = 0`, `v = c` when
`c` has no identity term) and bounded below by `0`, so the infimum is not a junk value. The
infimum need not be attained. -/
noncomputable def epsClose {Q : Type} [Fintype Q] [DecidableEq Q] (c : PauliWord Q → ℝ) : ℝ :=
  sInf {e : ℝ | ∃ u v : PauliWord Q → ℝ, IsDecomposition c u v ∧
    e = if v = 0 then 0 else wPert u v / (wFree u v + wPert u v)}

end QThermalClassical.Supplement


