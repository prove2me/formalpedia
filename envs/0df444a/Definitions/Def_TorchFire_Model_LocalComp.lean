-- Prove2me | Definitions.Def_TorchFire_Model_LocalComp
-- name    : TorchFire_Model_LocalComp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:35:49.180556+00:00
-- url     : https://prove2.me/theorems/0180f275-1ea1-4200-ad0a-50bae40f2b24
-- title:
--   The separated computations of §8.1, the witness sampler $E_i$, the filter $L_i$ and the step-4 extractor
-- statement:
--   The setting of the extraction lemma (§8.1, pp.59–64). At a location with input space $H$ and workspace $W$ (zero state $|0\rangle_W$):
--
--   1. common unitaries $G_0,\dots,G_q$ on $H\otimes W$, original and modified query unitaries $O^1_j,O^0_j$, the computations $U^1=G_qO^1_q\cdots G_1O^1_1G_0$ and $U^0$ (63), an acceptance projector $\Pi$, and the accepting maps $A=\Pi U^1J$, $C=\Pi U^0J$ with $J|\psi\rangle=|\psi\rangle|0\rangle_W$ (64);
--   2. a computational-basis diagonal witness projector $Q$ (65)–(66);
--   3. the prefixes $V_j=U^0_{<j}J$ ((67)–(68)), the **witness-sampler effect** $E=\frac1q\sum_{j=1}^qV_j^\dagger QV_j$ (69) and the **filter** $L=(I-E)^\beta$ (70);
--   4. the coherent sampler $VJ_0|\psi\rangle=q^{-1/2}\sum_j|j\rangle V_j|\psi\rangle$, $S=(VJ_0)(VJ_0)^\dagger$ and $T=I_R\otimes Q$ (pp.62–63);
--   5. the **success effect $W$ of the step-4 extractor** (p.63): append $J_0$, apply $V$, test $\{T,I-T\}$; after the first rejection perform at most $t=\lceil2\beta/\delta^2\rceil$ further rounds of $\{S,I-S\}$ (both outcomes continue) followed by $\{T,I-T\}$; stop on the first acceptance. $W$ is the sum of $K^\dagger K$ over the Kraus operators $K$ of the success branches, composed with $VJ_0$;
--   6. $\varepsilon_\beta=\sum_i\mathrm{Tr}(C_iL_i\rho_iL_iC_i^\dagger)$ (71) for $N$ locations and a joint input $\rho$.
--
--   **Formalization Note** $Q$ is a diagonal projector on $H\otimes W$ (paper.md decision 12: (65) multiplies it with operators on $H_i\otimes W_i$). $\varepsilon_\beta$ uses (71)'s order of $C_i$ and $L_i$ (decision 13). $W$ is the explicit procedure of step 4, not an arbitrary extractor (decision 14).
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), §8.1, (63)–(71) pp.59–60, step 2 (74) p.62, step 4 p.63

import Mathlib
import Definitions.Def_TorchFire_Model_OracleAlg
import Definitions.Def_TorchFire_Model_thresholdEffect

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix

namespace TorchFire.Model

/-- **One location of the separated computations** of §8.1 (Chatterjee–Mukherjee–Pathak–Podder,
*Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593,
pp.59–60, (63)–(66)). The input space is `H`, the workspace `W` with zero state `w0`.

* `G j` (`j = 0, …, q`) are the common unitaries `G_{i,j}` on `H ⊗ W`;
* `O1 j`, `O0 j` (`j = 0, …, q−1`, i.e. the queries `1, …, q`) are the original and modified
  oracle query unitaries `O^1_{i,j}`, `O^0_{i,j}`;
* `Pi` is the final acceptance projector `Π_i`;
* `wit` is the basis predicate of the computational-basis diagonal projector `Q_i` (66).

The hypotheses of Lemma 8.2 (unitarity, projectors, the witness condition (65)) are stated in the
lemma, not here.

**Formalization Note** `Q_i` is a diagonal projector on the query register, read as a diagonal
projector on `H ⊗ W` (paper.md decision 12): (65) multiplies it with operators on `H_i ⊗ W_i`, and
the proof applies it as `Q V_j` with `V_j : H_i → H_i ⊗ W_i` (p.61). -/
structure LocalComp (H : Type) where
  W : Type
  [instFintypeW : Fintype W]
  [instDecEqW : DecidableEq W]
  w0 : W
  G : ℕ → Matrix (H × W) (H × W) ℂ
  O1 : ℕ → Matrix (H × W) (H × W) ℂ
  O0 : ℕ → Matrix (H × W) (H × W) ℂ
  Pi : Matrix (H × W) (H × W) ℂ
  wit : H × W → Bool

attribute [instance] LocalComp.instFintypeW LocalComp.instDecEqW

namespace LocalComp

variable {H : Type} [Fintype H] [DecidableEq H] (C : LocalComp H) (q : ℕ)

/-- `J_i |ψ⟩ = |ψ⟩|0⟩_{W_i}` (p.59). -/
def J : Matrix (H × C.W) H ℂ := basisMat fun h => (h, C.w0)

/-- The original computation `U^1_i = G_{i,q} O^1_{i,q} ⋯ G_{i,1} O^1_{i,1} G_{i,0}` (63). -/
def U1 : Matrix (H × C.W) (H × C.W) ℂ := evolve C.G C.O1 q

/-- The modified computation `U^0_i` (63). -/
def U0 : Matrix (H × C.W) (H × C.W) ℂ := evolve C.G C.O0 q

/-- The accepting map of the original computation, `A_i = Π_i U^1_i J_i` (64). -/
def Amap : Matrix (H × C.W) H ℂ := C.Pi * C.U1 q * C.J

/-- The accepting map of the modified computation, `C_i = Π_i U^0_i J_i` (64). -/
def Cmap : Matrix (H × C.W) H ℂ := C.Pi * C.U0 q * C.J

/-- The witness projector `Q_i` (65), (66). -/
def Qmat : Matrix (H × C.W) (H × C.W) ℂ := Matrix.diagonal fun s => if C.wit s then 1 else 0

/-- `V_{i,j} = U^0_{i,<j} J_i` ((67), (68)), for the `0`-based query index `j`: the modified
computation run up to just before query `j + 1`. -/
def V (j : ℕ) : Matrix (H × C.W) H ℂ := evolve C.G C.O0 j * C.J

/-- **The witness-sampler effect** `E_i = (1/q) Σ_{j=1}^q V_{i,j}† Q_i V_{i,j}` (69). -/
noncomputable def Emat : Matrix H H ℂ :=
  ((q : ℂ))⁻¹ • ∑ j ∈ Finset.range q, (C.V j)ᴴ * C.Qmat * C.V j

/-- **The filter** `L_i = (I − E_i)^β` (70). -/
noncomputable def Lmat (β : ℕ) : Matrix H H ℂ := (1 - C.Emat q) ^ β

/-- The coherent sampler on the input: `V J_0 |ψ⟩ = q^{−1/2} Σ_j |j⟩_R V_j |ψ⟩` (§8.1 step 2, p.62),
an isometry `H → R ⊗ H ⊗ W` with `R` indexed by the query positions. -/
noncomputable def VJ0 : Matrix (Fin q × (H × C.W)) H ℂ :=
  Matrix.of fun x h => ((Real.sqrt q : ℝ) : ℂ)⁻¹ * C.V x.1 x.2 h

/-- `S = V Π_0 V† = (V J_0)(V J_0)†` (§8.1 step 4, p.63). -/
noncomputable def Sproj : Matrix (Fin q × (H × C.W)) (Fin q × (H × C.W)) ℂ :=
  C.VJ0 q * (C.VJ0 q)ᴴ

/-- `T = Π_Q = I_R ⊗ Q` ((74), p.62; step 4, p.63). -/
def Tproj : Matrix (Fin q × (H × C.W)) (Fin q × (H × C.W)) ℂ :=
  Matrix.diagonal fun x => if C.wit x.2 then 1 else 0

/-- The outcome operator of one `{S, I − S}` measurement (`true` = `S`). -/
noncomputable def Sout (o : Bool) : Matrix (Fin q × (H × C.W)) (Fin q × (H × C.W)) ℂ :=
  if o then C.Sproj q else 1 - C.Sproj q

/-- The unnormalized branch after the first rejection and the further rounds with `S`-outcomes
`os` (in order), each followed by a rejecting witness test:
`(I − T) P_{o_r} ⋯ (I − T) P_{o_1} (I − T)`. -/
noncomputable def rejBranch (os : List Bool) : Matrix (Fin q × (H × C.W)) (Fin q × (H × C.W)) ℂ :=
  os.foldl (fun M o => (1 - C.Tproj q) * C.Sout q o * M) (1 - C.Tproj q)

/-- **The success effect `W_i` of the witness extractor of §8.1 step 4** (p.63; paper.md
decision 14). The extractor appends `J_0`, applies `V` and tests `{T, I − T}`; on acceptance it
outputs the measured query (a witness). After the first rejection it performs at most
`t = ⌈2β/δ²⌉` further rounds, each measuring `{S, I − S}` (both outcomes continue) and then testing
`{T, I − T}`. `W_i` is the sum, over the success branches, of `K†K` for the branch's Kraus operator
`K` composed with `V J_0`:

* first test: `K = T`;
* round `r ∈ {1, …, t}` with `S`-outcomes `o_1, …, o_r`: `K = T P_{o_r} (I−T) P_{o_{r−1}} ⋯ (I−T)`.

It is built only from `V_{i,j}` (via `V J_0`), `Q_i`, `β` and `δ`, so the extractor is the explicit
local procedure of the lemma, not an arbitrary one. -/
noncomputable def extractorEffect (β : ℕ) (δ : ℝ) : Matrix H H ℂ :=
  let t := ⌈2 * (β : ℝ) / δ ^ 2⌉₊
  let K0 := C.Tproj q * C.VJ0 q
  K0ᴴ * K0 +
    ∑ r ∈ Finset.range t, ∑ os : Fin (r + 1) → Bool,
      let K := C.Tproj q * C.Sout q (os (Fin.last r)) *
        C.rejBranch q (List.ofFn (Fin.init os)) * C.VJ0 q
      Kᴴ * K

end LocalComp

/-- **The filtered modified acceptance** `ε_β = Σ_{i=1}^N Tr(C_i L_i ρ_i L_i C_i†)` ((71), p.60, at
fixed oracles; paper.md decision 13: (71)'s order of `C_i` and `L_i`). -/
noncomputable def epsBeta {N : ℕ} {H : Fin N → Type} [∀ i, Fintype (H i)] [∀ i, DecidableEq (H i)]
    (C : (i : Fin N) → LocalComp (H i)) (q β : ℕ)
    (ρ : Matrix ((i : Fin N) → H i) ((i : Fin N) → H i) ℂ) : ℝ :=
  ∑ i, (Matrix.trace (conjMat ((C i).Cmap q * (C i).Lmat q β) (reducedAt ρ i))).re

end TorchFire.Model


