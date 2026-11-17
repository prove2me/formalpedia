-- Prove2me | Definitions.Def_QDSGibbs_Supplement_fhLattice
-- name    : QDSGibbs_Supplement_fhLattice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:26:27.002042+00:00
-- url     : https://prove2.me/theorems/b335a149-8f79-4131-9c71-c474032ffd7e
-- title:
--   Fermi–Hubbard model on $\Lambda\subset\mathbb Z^D$: $H$, $t_{\max}$, $U_{\max}$, $\omega_{\max}$, labelled cubes, $H_B$, $W_{\partial B}$, Majoranas
-- statement:
--   Let $\Lambda\subset\mathbb Z^D$ be finite, with nearest-neighbour edges $E=\{\{i,j\}:|i-j|_1=1\}$ and two fermionic modes $c_{i,\uparrow},c_{i,\downarrow}$ per site.
--
--   1. The **Fermi–Hubbard Hamiltonian** (7.12) $$H=-\sum_{\{i,j\}\in E}t_{ij}\sum_{s}(c^*_{i,s}c_{j,s}+c^*_{j,s}c_{i,s})+\sum_{i\in\Lambda}\bigl[U_in_{i,\uparrow}n_{i,\downarrow}+\mu_i(n_{i,\uparrow}+n_{i,\downarrow})\bigr],$$ with $t_{\max}=\max_E|t_{ij}|$ ($0$ if $E=\emptyset$), $U_{\max}=\max_i|U_i|$ and $\omega_{\max}=\tfrac12\bigl(\max_i(\mu_i+U_i/2)-\min_i(\mu_i+U_i/2)\bigr)$ (7.14).
--   2. The **labelled cubes** $B_z=\Lambda\cap(z+\{0,\dots,\ell-1\}^D)$, $z\in\mathbb Z^D$, of which only the nonempty ones are used.
--   3. For a block $B$: $H_B$ the terms supported in $B$, $H^0_B=H_B+H_{B^c}$ and $W_{\partial B}=H-H^0_B$.
--   4. The **Majoranas** $\gamma_{i,s,1}=c_{i,s}+c^*_{i,s}$ and $\gamma_{i,s,2}=i(c^*_{i,s}-c_{i,s})$.
--   5. The loss factor $\beta U_{\max}[1+\log(4/(\beta U_{\max}))]^{4D}$ of (7.19), given its continuous value $0$ at $U_{\max}=0$.
--
--   **Formalization Note** The Hamiltonian is the published `FermiHubbardMix.fhHam` (Bakshi–Moitra–Tan, the same model) on the nearest-neighbour graph; operators act on the Fock space of the $M=2|\Lambda|$ modes in a Jordan–Wigner ordering `ord`, with $c$ the published `GaussTesting.annihilator`. The labels of nonempty cubes are $z=i-o$, $i\in\Lambda$, $o\in\{0,\dots,\ell-1\}^D$.
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), §7 pp.62, 65–66, (7.12) and (7.14) p.65, cubes p.66, (7.19) p.67

import Mathlib
import Definitions.Def_FermiHubbardMix_fermiHubbard

open scoped Matrix

namespace QDSGibbs.Supplement

/-- The **nearest-neighbour graph** of a finite lattice `Λ ⊂ ℤ^D`: `E = {{i, j} : |i − j|₁ = 1}`
(Rouzé–Stilck França, arXiv:2610.03578, held file sha256 ede55815…, §7, p.65). -/
def latticeGraph {D : ℕ} (Λ : Finset (Fin D → ℤ)) : SimpleGraph Λ :=
  SimpleGraph.fromRel fun i j => ∑ k, |i.1 k - j.1 k| = 1

open Classical in
/-- The **Fermi–Hubbard Hamiltonian** (7.12) on a finite `Λ ⊂ ℤ^D` (arXiv:2610.03578, p.65):
`H = −Σ_{{i,j} ∈ E} t_ij Σ_s (c*_{i,s} c_{j,s} + c*_{j,s} c_{i,s}) + Σ_i [U_i n_{i,↑} n_{i,↓}
+ µ_i (n_{i,↑} + n_{i,↓})]`, with `E` the nearest-neighbour edges.

**Formalization Note** This is the published `FermiHubbardMix.fhHam` (Bakshi–Moitra–Tan,
Example 11.8, the same Hamiltonian) on the graph `latticeGraph Λ`. Two modes per site, spin `↑` is
mode `0`, `↓` is mode `1`; `ord : Λ × Fin 2 ≃ Fin M` is the fixed Jordan–Wigner ordering of the
`M = 2|Λ|` modes, and the Fock space is `ℂ^{2^M}` (local dimension `4` per site). The hopping
amplitudes are one real `t e` per unordered pair `e`; only edges are used. -/
noncomputable def fhLattice {D M : ℕ} (Λ : Finset (Fin D → ℤ)) (ord : Λ × Fin 2 ≃ Fin M)
    (t : Sym2 Λ → ℝ) (U μ : Λ → ℝ) : FermiHubbardMix.HamData Λ M :=
  FermiHubbardMix.fhHam ord (latticeGraph Λ) t U μ

open Classical in
/-- `t_max = max_{{i,j} ∈ E} |t_ij|`, with `t_max = 0` when `E = ∅` (arXiv:2610.03578, p.65); the
published `FermiHubbardMix.tmax` on the nearest-neighbour graph. -/
noncomputable def tMaxL {D : ℕ} (Λ : Finset (Fin D → ℤ)) (t : Sym2 Λ → ℝ) : ℝ :=
  FermiHubbardMix.tmax (latticeGraph Λ) t

/-- `U_max = max_i |U_i|` (arXiv:2610.03578, p.65).

**Formalization Note** A real supremum over the finite set of sites (a maximum for `Λ ≠ ∅`). -/
noncomputable def uMax {Λ : Type} [Fintype Λ] (U : Λ → ℝ) : ℝ := ⨆ i, |U i|

/-- The half-width of the effective on-site potential
`ω_max = ½ (max_i (µ_i + U_i/2) − min_i (µ_i + U_i/2))` (arXiv:2610.03578, (7.14), p.65). -/
noncomputable def omegaMax {Λ : Type} [Fintype Λ] (U μ : Λ → ℝ) : ℝ :=
  ((⨆ i, (μ i + U i / 2)) - ⨅ i, (μ i + U i / 2)) / 2

/-- The interaction loss factor `βU_max [1 + log(4/(βU_max))]^{4D}` of (7.19) (arXiv:2610.03578,
p.67), given its continuous value `0` at `βU_max = 0` ("At `U_max = 0`, the expression … is
interpreted by its continuous value zero"). -/
noncomputable def uLoss (D : ℕ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else x * (1 + Real.log (4 / x)) ^ (4 * D)

/-- The **labelled cube** `B_z = Λ ∩ (z + {0, …, ℓ−1}^D)` (arXiv:2610.03578, p.66). -/
def cube {D : ℕ} (Λ : Finset (Fin D → ℤ)) (ℓ : ℕ) (z : Fin D → ℤ) : Finset Λ :=
  Finset.univ.filter fun i => ∀ k, z k ≤ i.1 k ∧ i.1 k < z k + ℓ

/-- The labels `z ∈ ℤ^D` of the **nonempty** cubes `B_z` (arXiv:2610.03578, p.66: "all nonempty
labelled cubes"): `z = i − o` with `i ∈ Λ`, `o ∈ {0, …, ℓ−1}^D`. Distinct labels are distinct blocks
of the family even if the sets coincide. -/
def cubeLabels {D : ℕ} (Λ : Finset (Fin D → ℤ)) (ℓ : ℕ) : Finset (Fin D → ℤ) :=
  (Λ ×ˢ Fintype.piFinset (fun _ : Fin D => Finset.range ℓ)).image
    fun p => fun k => p.1 k - (p.2 k : ℤ)

/-- The **block Hamiltonian** `H_B`: the terms of `H` supported in `B` (arXiv:2610.03578, p.65),
`H_B = Σ_{i ∈ B} v_i + Σ_{Z ⊆ B, |Z| ≥ 2} w_Z`. -/
noncomputable def hamOnF {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : ℕ}
    (H : FermiHubbardMix.HamData Λ M) (B : Finset Λ) : FermiHubbardMix.Op M :=
  ∑ i ∈ B, H.v i + ∑ Z ∈ Finset.univ.filter (fun Z : Finset Λ => 2 ≤ Z.card ∧ Z ⊆ B), H.w Z

/-- The **crossing interaction** `W_∂B = H − H⁰_B`, `H⁰_B = H_B + H_{B^c}` (arXiv:2610.03578,
p.65). -/
noncomputable def crossF {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : ℕ}
    (H : FermiHubbardMix.HamData Λ M) (B : Finset Λ) : FermiHubbardMix.Op M :=
  H.ham - hamOnF H B - hamOnF H Bᶜ

/-- The **Majorana operators** `γ_{i,s,1} = c_{i,s} + c*_{i,s}`, `γ_{i,s,2} = i(c*_{i,s} − c_{i,s})`
(arXiv:2610.03578, p.62).

**Formalization Note** The component `r ∈ {1, 2}` is `Fin 2` (`0 ↦ 1`, `1 ↦ 2`); `c_{i,s}` is the
published `GaussTesting.annihilator M (ord (i, s))`. -/
noncomputable def majF {Λ : Type} {M : ℕ} (ord : Λ × Fin 2 ≃ Fin M) (i : Λ) (s r : Fin 2) :
    FermiHubbardMix.Op M :=
  if r = 0 then
    GaussTesting.annihilator M (ord (i, s)) + (GaussTesting.annihilator M (ord (i, s)))ᴴ
  else
    Complex.I • ((GaussTesting.annihilator M (ord (i, s)))ᴴ - GaussTesting.annihilator M (ord (i, s)))

end QDSGibbs.Supplement


