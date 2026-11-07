-- Prove2me | Definitions.Def_CritWinSpin_BinarySource
-- name    : CritWinSpin_BinarySource
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:40:15.559145+00:00
-- url     : https://prove2.me/theorems/024f53e2-eb3f-4adc-9240-2e63d17ef919
-- title:
--   Binary Ising source, its properties (i)–(iii), the verification circuit, and the zero-field source
-- statement:
--   A **binary Ising source** over a bilinear family assigns to each $d$ and each Waters key a rational model $H_P(y)=\frac12y^\top J_0y+h_0^\top y$ on $\{\pm1\}^{n}$, a valid set $\Omega_P$ and a message map $\Psi_P:\{\pm1\}^n\to\{0,1\}^d$; $n_0$ is the number of circuit wires. With $\mu_P=e^{H_P}/Z_{H_P}$ and $V_P=\mathrm{Unif}(\Omega_P)$, the predicate `SourceProps` says that for $d\ge1$ and every key:
--
--   1. $J_0$ is symmetric with zero diagonal, $\mathrm{wd}(J_0,h_0)\le n^w$, and $P\mapsto H_P$, $(P,F)\mapsto\Psi_P(F)$ are polynomial-time;
--   2. (i) $\mathrm{TV}(\mu_P,V_P)\le e^{-n_0^2}$ and $\mathrm{TV}(V_P^{\otimes T},\mu_P^{\otimes T})\le Te^{-n_0^2}$;
--   3. (ii) $\Psi_P(F)$ is uniform under $V_P$, every randomized predictor of $\Psi_P(F_i)$ from $F_{-i}$ succeeds with probability exactly $2^{-d}$, and a collision among $\Psi_P(F_1),\dots,\Psi_P(F_T)$ has probability at most $\binom T22^{-d}$;
--   4. (iii) for every PPT $A$ and efficiently computable polynomial $T\ge1$ there is a PPT $B$ with, for all large $d$,
--   $$\mathbb P\{A(P,F_{1:T})=F^*\in\Omega_P,\ \Psi_P(F^*)\notin\{\Psi_P(F_t)\}\}\le C\,T\sqrt d\,\mathrm{Adv}_{\mathrm{CDH}}(B).$$
--
--   A **verification circuit** gives the wire configurations of $C_{\mathrm{ver}}$ on $P$ and a message–signature pair, with $\Omega_P$ the configurations of valid triples. The **zero-field source** on $n+1$ spins is $\hat H_P(t,z)=H_P(tz)$, $\hat\Omega_P=\{(t,z):tz\in\Omega_P\}$, $\hat\Psi_P(t,z)=\Psi_P(tz)$.
--
--   **Formalization Note** The paper does not give the circuit, and no later statement depends on its gates, so it enters as data with the properties used. $T$ is efficiently computable because the uniform $B$ has to simulate $T$ samples.
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), §5.2, pp.18–19, eq. (26); Theorem 5.1, p.19; §7, p.26

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_CritWinSpin_encInst
import Definitions.Def_CritWinSpin_pkCode
open QAlgorithms.Complexity QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
set_option autoImplicit false

namespace CritWinSpin

/-- A binary spin configuration on `n` sites; `true` is `+1`, `false` is `−1`. -/
abbrev BinCfg (n : ℕ) : Type := Fin n → Bool

/-- The sign of a binary spin: `spinOf true = 1`, `spinOf false = −1` (§5.2, p.18). -/
def spinOf (b : Bool) : ℝ := if b then 1 else -1

/-- The real spin vector of a binary configuration. -/
noncomputable def binVec {n : ℕ} (y : BinCfg n) : Fin n → ℝ := fun i => spinOf (y i)

/-- The binary Gibbs measure `μ_H(y) = e^{H(y)} / Z_H` of `H(y) = ½ yᵀJ₀y + h₀ᵀy` on `{±1}^n`
(Theorem 5.1, p.19; §6.1, p.21). -/
noncomputable def muH {n : ℕ} (J₀ : Matrix (Fin n) (Fin n) ℝ) (h₀ : Fin n → ℝ) (y : BinCfg n) : ℝ :=
  Real.exp (energy J₀ h₀ (binVec y)) / ∑ y' : BinCfg n, Real.exp (energy J₀ h₀ (binVec y'))

/-- The uniform distribution on a finite set. -/
noncomputable def unifOn {α : Type} (Ω : Finset α) (x : α) : ℝ :=
  open Classical in if x ∈ Ω then 1 / (Ω.card : ℝ) else 0

/-- The product law `μ^{⊗T}`. -/
noncomputable def prodLaw {α : Type} (μ : α → ℝ) {T : ℕ} (F : Fin T → α) : ℝ := ∏ t, μ (F t)

/-- **The data of a binary Ising source** `(H, Ω, Ψ)` over Waters keys (Theorem 5.1, p.19; §7, p.26):
for each `1^d` and each key, a rational model `H_P` on `n(d)` spins, a valid set `Ω_P` and a message
map `Ψ_P`. `n0 d` is the number of wires of the verification circuit, which is the exponent of the
error of (i).

Source: Liu–Zhang–Ren, STOC 2027 submission (manuscript sha256 f77584da…), §5.2, p.18; §7, p.26. -/
structure BinarySource (F : BilinearFamily) where
  /-- The number `n₀` of circuit wires. -/
  n0 : ℕ → ℕ
  /-- The number `n` of spins (`n₀` or `n₀ + 1`). -/
  n : ℕ → ℕ
  /-- The model `H_P = (J₀, h₀)`. -/
  ham : (d : ℕ) → (desc : Str) → WatersKey F desc d → Inst (n d)
  /-- The valid set `Ω_P`. -/
  omega : (d : ℕ) → (desc : Str) → WatersKey F desc d → Finset (BinCfg (n d))
  /-- The message map `Ψ_P`. -/
  psi : (d : ℕ) → (desc : Str) → WatersKey F desc d → BinCfg (n d) → Fin d → Bool

/-- The probability (27) that `A(P, F_{1:T})` outputs a configuration `F* ∈ Ω_P` with
`Ψ_P(F*) ∉ {Ψ_P(F_1), …, Ψ_P(F_T)}`, over `(P, K) ← KeyGen(1^d)`, `F_{1:T} ∼ V_P^{⊗T}` and the coins
of `A` (Theorem 5.1(iii), p.19). -/
noncomputable def forgeProb {F : BilinearFamily} (src : BinarySource F) (A : PPT) (T d : ℕ) : ℝ :=
  keygenAvg F d fun desc key =>
    ∑ Fs : Fin T → BinCfg (src.n d), prodLaw (unifOn (src.omega d desc key)) Fs *
      A.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t => List.ofFn (Fs t)))
        (fun s => ∃ y : BinCfg (src.n d), s = List.ofFn y ∧ y ∈ src.omega d desc key ∧
          ∀ t, src.psi d desc key y ≠ src.psi d desc key (Fs t))

/-- **The properties of a binary Ising source** with cryptographic constant `C` (Theorem 5.1,
pp.19–20), for `d ≥ 1` and every key in the support of `KeyGen(1^d)`:
zero-diagonal symmetric model of polynomial width; the maps `P ↦ H_P` and `(P, F) ↦ Ψ_P(F)` are
polynomial-time;
(i) `TV(μ_P, V_P) ≤ e^{−n₀²}` and `TV(V_P^{⊗T}, μ_P^{⊗T}) ≤ T e^{−n₀²}`;
(ii) `Ψ_P(F)` is uniform for `F ∼ V_P`, every randomized predictor of `Ψ_P(F_i)` from `F_{−i}` succeeds
with probability exactly `2^{−d}`, and a message collision has probability at most
`(T choose 2) 2^{−d}`;
(iii) the bound (27): for every PPT `A` and every efficiently computable polynomial `T ≥ 1` there is
a PPT `B` with `forgeProb ≤ C · T · √d · Adv_CDH(B)` for all large `d`.

**Formalization Note.** A randomized predictor is a stochastic kernel from `F_{−i}` to messages; `P`
is fixed, so dependence on `P` is free and no efficiency is required, as on p.19. `T` must be
efficiently computable because `B` is a uniform algorithm that has to simulate `T` samples. The
constant `C` is a parameter: Theorem 5.1 asserts its existence before the adversary. -/
def SourceProps (F : BilinearFamily) (src : BinarySource F) (C : ℝ) : Prop :=
  (∃ w : ℕ, 1 ≤ w ∧ ∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
    (src.ham d desc key).1.IsSymm ∧ (∀ i, (src.ham d desc key).1 i i = 0) ∧
    width (castM (src.ham d desc key).1) (castV (src.ham d desc key).2) ≤ ((src.n d : ℝ)) ^ w) ∧
  (∃ hamF : Str → Str, CookPvsNP.PolyTimeComputable hamF ∧
    ∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
      hamF (pkCode F d desc key) = encInst (src.ham d desc key)) ∧
  (∃ psiF : Str → Str, CookPvsNP.PolyTimeComputable psiF ∧
    ∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ (key : WatersKey F desc d) (y : BinCfg (src.n d)),
      psiF (tupleCode [pkCode F d desc key, List.ofFn y]) = List.ofFn (src.psi d desc key y)) ∧
  (∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
    let μ := muH (castM (src.ham d desc key).1) (castV (src.ham d desc key).2)
    let V := unifOn (src.omega d desc key)
    let Ψ := src.psi d desc key
    -- (i)
    tvDist μ V ≤ Real.exp (-((src.n0 d : ℝ) ^ 2)) ∧
    (∀ T : ℕ, 1 ≤ T → tvDist (prodLaw V (T := T)) (prodLaw μ (T := T)) ≤
      (T : ℝ) * Real.exp (-((src.n0 d : ℝ) ^ 2))) ∧
    -- (ii)
    (∀ m₀ : Fin d → Bool, ∑ y, V y * (if Ψ y = m₀ then (1 : ℝ) else 0) = 1 / (2 : ℝ) ^ d) ∧
    (∀ (T : ℕ) (i : Fin T)
      (pred : ({j : Fin T // j ≠ i} → BinCfg (src.n d)) → (Fin d → Bool) → ℝ),
      (∀ x m, 0 ≤ pred x m) → (∀ x, ∑ m, pred x m = 1) →
      ∑ Fs : Fin T → BinCfg (src.n d), prodLaw V Fs * pred (fun j => Fs j) (Ψ (Fs i)) =
        1 / (2 : ℝ) ^ d) ∧
    (∀ T : ℕ, ∑ Fs : Fin T → BinCfg (src.n d), prodLaw V Fs *
        (open Classical in if Function.Injective (fun t => Ψ (Fs t)) then (0 : ℝ) else 1) ≤
      (T.choose 2 : ℝ) * (1 / (2 : ℝ) ^ d))) ∧
  -- (iii)
  (∀ (A : PPT) (T : ℕ → ℕ), EffPoly T → (∀ d, 1 ≤ T d) →
    ∃ B : PPT, ∃ d₀ : ℕ, ∀ d ≥ d₀,
      forgeProb src A (T d) d ≤ C * (T d : ℝ) * Real.sqrt (d : ℝ) * cdhAdv F B d)

/-- **The verification circuit, as data** (§5.2, pp.18–19): the number `n₀` of wires; the
wire configuration `evalCfg` obtained by evaluating `C_ver` on `P` and a message–signature pair; the
message bits `psi`; and the Ising model `ham` of the embedding.

**Formalization Note.** The paper does not give the circuit, and no later statement depends on its
gates; Theorem 5.1 is therefore existential over this data, with the properties the paper uses. -/
structure WatersCircuit (F : BilinearFamily) where
  /-- The number of wires. -/
  n0 : ℕ → ℕ
  /-- The Ising model of the circuit embedding. -/
  ham : (d : ℕ) → (desc : Str) → WatersKey F desc d → Inst (n0 d)
  /-- The wire values of `C_ver` on `(P, m, g^{s₁}, g^{s₂})`. -/
  evalCfg : (d : ℕ) → (desc : Str) → (key : WatersKey F desc d) → (Fin d → Bool) →
    ZMod (F.q desc) → ZMod (F.q desc) → BinCfg (n0 d)
  /-- The message bits `Ψ_P` of a wire configuration. -/
  psi : (d : ℕ) → (desc : Str) → WatersKey F desc d → BinCfg (n0 d) → Fin d → Bool

open Classical in
/-- `Ω_P`: the configurations obtained by evaluating `C_ver` on `P` and a valid message–signature
pair (§5.2, p.18). -/
noncomputable def WatersCircuit.omega {F : BilinearFamily} (C : WatersCircuit F) (d : ℕ) (desc : Str)
    (key : WatersKey F desc d) : Finset (BinCfg (C.n0 d)) :=
  Finset.univ.filter fun y => ∃ (m : Fin d → Bool) (s₁ s₂ : ZMod (F.q desc)),
    IsValidSig key m s₁ s₂ ∧ y = C.evalCfg d desc key m s₁ s₂

/-- The source `(H_P, Ω_P, Ψ_P)` of a circuit, on `n = n₀` spins (Theorem 5.1, p.19). -/
noncomputable def WatersCircuit.toSource {F : BilinearFamily} (C : WatersCircuit F) :
    BinarySource F where
  n0 := C.n0
  n := C.n0
  ham := C.ham
  omega := C.omega
  psi := C.psi

/-- The law of the Waters generation in Theorem 5.1(ii), p.19: the probability that drawing
`m ∼ Unif({0,1}^d)`, `r ∼ Unif(ℤ_q)`, signing and evaluating `C_ver` gives the configuration `y`. -/
noncomputable def WatersCircuit.genLaw {F : BilinearFamily} (C : WatersCircuit F) (d : ℕ)
    (desc : Str) (key : WatersKey F desc d) (y : BinCfg (C.n0 d)) : ℝ :=
  open Classical in
  (1 / ((2 : ℝ) ^ d * (F.q desc : ℝ))) * ∑ m : Fin d → Bool, ∑ r : Fin (F.q desc),
    if C.evalCfg d desc key m (expo r) (signS2 key m (expo r)) = y then (1 : ℝ) else 0

/-- The product configuration `tz` of `(t, z) ∈ {±1} × {±1}^n`, §5.2, p.19, with
`spinOf (t == b) = spinOf t * spinOf b`. -/
def hatProd {n : ℕ} (y : BinCfg (n + 1)) : BinCfg n := fun i => y 0 == y i.succ

/-- The matrix `Ĵ₀` of (26), p.19, on `n + 1` spins with the extra spin `t` at index `0`:
`½ (t, z)ᵀ Ĵ₀ (t, z) = ½ zᵀJ₀z + t h₀ᵀz`, and the field is `0`. -/
def hatInst {n : ℕ} (M : Inst n) : Inst (n + 1) :=
  (Matrix.of fun i j => Fin.cases (Fin.cases 0 M.2 j) (fun i' => Fin.cases (M.2 i') (M.1 i') j) i,
    fun _ => 0)

open Classical in
/-- **The zero-field source** `(Ĥ_P, Ω̂_P, Ψ̂_P)` on `n + 1` spins, eq. (26), p.19:
`Ĥ_P(t, z) = H_P(tz)`, `Ω̂_P = {(t, z) : tz ∈ Ω_P}`, `Ψ̂_P(t, z) = Ψ_P(tz)`.

Source: Liu–Zhang–Ren, STOC 2027 submission (manuscript sha256 f77584da…), eq. (26), p.19. -/
noncomputable def hatSource {F : BilinearFamily} (src : BinarySource F) : BinarySource F where
  n0 := src.n0
  n := fun d => src.n d + 1
  ham := fun d desc key => hatInst (src.ham d desc key)
  omega := fun d desc key => Finset.univ.filter fun y => hatProd y ∈ src.omega d desc key
  psi := fun d desc key y => src.psi d desc key (hatProd y)

end CritWinSpin


