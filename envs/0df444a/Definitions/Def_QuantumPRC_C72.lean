-- Prove2me | Definitions.Def_QuantumPRC_C72
-- name    : QuantumPRC_C72
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:38:57.851704+00:00
-- url     : https://prove2.me/theorems/5edb7574-50b8-4370-b035-061c823c2a0f
-- title:
--   Construction 7.2 (PRIC): $V_{\mathsf{sk}_{\mathrm{in}}}$, $\mathsf{BitDec}$, $\Pi^{\mathsf{Good}}$, and the channel-level scheme
-- statement:
--   Fix $n_{\mathrm L},\ell,r,m$ and $n_{\mathrm P}=n_{\mathrm L}+\ell+r+m$; registers are $A$ ($n_{\mathrm L}$ qubits), $B$ ($n_{\mathrm L}+\ell+r$), $C$ ($m$), $D$ ($n_{\mathrm L}+\ell$). The ingredients are an $(n_{\mathrm L}+\ell,m)$ PRFC with encoder $g_{\mathsf{sk}'}$ and decoder $\mathsf{PRFC.Dec}(\mathsf{sk}',\cdot)$, keyed functions $f_k:\{0,1\}^{n_{\mathrm L}+\ell}\to\{0,1\}$ (a PRF), keyed permutations $\pi_{k'}$ of $\{0,1\}^{n_{\mathrm L}+\ell+r}$ (a PRP), and GraphSample, Recover.
--
--   1. $V_{\mathsf{sk}_{\mathrm{in}}}:|x\rangle_A\mapsto\frac1{\sqrt{2^\ell}}\sum_{y}(-1)^{f_k(x\|y)}|\pi_{k'}(x\|y\|0^r)\rangle_B|g_{\mathsf{sk}'}(x\|y)\rangle_C$ (111); $c(z):=\pi_{k'}(z\|0^r)\|g_{\mathsf{sk}'}(z)$.
--   2. $\mathsf{BitDec}$: $|c\rangle_C\mapsto|c\rangle_C|\mathsf{PRFC.Dec}(\mathsf{sk}',c)\rangle_D$, then $|b\rangle_B|c\rangle_C|z\rangle_D\mapsto(-1)^{f_k(z)}|b\oplus\pi_{k'}(z\|0^r)\rangle_B|c\oplus g_{\mathsf{sk}'}(z)\rangle_C|z\rangle_D$ (117)–(118).
--   3. $\Pi^{\mathsf{Good}}_{BCD}=|e\rangle\langle e|_{BC}\otimes I_D$ (126).
--   4. **KeyGen**: $\mathsf{sk}'\leftarrow\mathsf{PRFC.KeyGen}(1^\lambda)$, $k,k'\leftarrow\{0,1\}^\lambda$, $G\leftarrow\mathsf{GraphSample}(1^{n_{\mathrm P}/2})$, $P\leftarrow\mathcal P_{n_{\mathrm P}}$; $\mathsf{sk}=(\mathsf{sk}',k,k',G,P)$.
--   5. **Enc**: the isometry $\mathrm{Enc}_{\mathsf{sk}}=(PU_G)_{BC}\circ V_{\mathsf{sk}_{\mathrm{in}}}$ (110).
--   6. **Dec**: apply $U_G^\dagger P^\dagger$, then $\mathsf{BitDec}$; measure $BC$ to get $e$, compute $u=\mathsf{Recover}(G,e)$, apply $|z\rangle_D\mapsto(-1)^{u\cdot c(z)}|z\rangle_D$, and output the first $n_{\mathrm L}$ qubits of $D$.
--
--   The resulting scheme is a channel-level secret-key code from $n_{\mathrm L}$ to $n_{\mathrm P}$ qubits; GraphSample and Recover read the scheme parameter $W$ as their radius.
--
--   **Formalization Note** GraphSample is given by its coins. KeyGen's coins are split, in order, among PRFC.KeyGen, $k$, $k'$, GraphSample and the Pauli $P=i^{2b_0+b_1}X^xZ^z$ (uniform on $\mathcal P_{n_{\mathrm P}}$). Dec is written in Kraus form $\sum_{e,y}K_{e,y}\rho K_{e,y}^\dagger$, $y$ ranging over the traced last $\ell$ qubits of $D$. The paper takes $n_{\mathrm P}$ even; for odd $n_{\mathrm P}$ the graph lives on the first $2\lfloor n_{\mathrm P}/2\rfloor$ vertices, Recover reads the first $2\lfloor n_{\mathrm P}/2\rfloor$ bits of $e$ and $u$ is padded with $0$.
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Construction 7.2, Eqs. (110)–(119), pp.41–42; Eq. (126), p.43; Claim 7.8, p.44

import Mathlib
import Definitions.Def_QuantumPRC_ChScheme
import Definitions.Def_QuantumPRC_PRFC
import Definitions.Def_QuantumPRC_GraphRecoverSpec
import Definitions.Def_QuantumPRC_pfIso

open Matrix

namespace QuantumPRC

section Raw

variable {nL ℓ r m : ℕ}

/-- `c(z) := π(z∥0^r) ∥ g(z)` (Claim 7.8, p.44), a string of `nL + ℓ + r + m` bits. -/
def cwVec (π : Equiv.Perm (Bits (nL + ℓ + r))) (g : Bits (nL + ℓ) → Bits m) (z : Bits (nL + ℓ)) :
    Bits (nL + ℓ + r + m) :=
  Fin.append (π (Fin.append z (zeros r))) (g z)

/-- **The isometry `V_{sk_in}`**, Eq. (111), p.41: `|x⟩_A ↦ (1/√2^ℓ) Σ_{y∈{0,1}^ℓ} (−1)^{f(x∥y)}
|π(x∥y∥0^r)⟩_B |g(x∥y)⟩_C`, for arbitrary `f`, `π`, `g` (in the construction `f = f_k`, `π = π_{k′}`,
`g = g_{sk′} = PRFC.Enc(sk′, ·)`). Register order: `B` (`nL + ℓ + r` qubits) then `C` (`m` qubits). -/
noncomputable def vSkin (f : Bits (nL + ℓ) → Bool) (π : Equiv.Perm (Bits (nL + ℓ + r)))
    (g : Bits (nL + ℓ) → Bits m) : Matrix (Bits (nL + ℓ + r + m)) (Bits nL) ℂ :=
  fun s x => ((Real.sqrt 2 : ℂ) ^ ℓ)⁻¹ * ∑ y : Bits ℓ,
    if s = cwVec π g (Fin.append x y) then (if f (Fin.append x y) then -1 else 1) else 0

/-- **The isometry `BitDec_{sk_in, BC→BCD}`**, Step 2 of Dec, Eqs. (117)–(118), p.41: first
`|c⟩_C ↦ |c⟩_C |PRFC.Dec(sk′, c)⟩_D`, then `|b⟩_B |c⟩_C |z⟩_D ↦ (−1)^{f(z)} |b ⊕ π(z∥0^r)⟩_B |c ⊕ g(z)⟩_C |z⟩_D`;
here for arbitrary `f, π, g` and an arbitrary decoder `dec`. Output index: `(BC, D)`. -/
noncomputable def bitDec (f : Bits (nL + ℓ) → Bool) (π : Equiv.Perm (Bits (nL + ℓ + r)))
    (g : Bits (nL + ℓ) → Bits m) (dec : Bits m → Bits (nL + ℓ)) :
    Matrix (Bits (nL + ℓ + r + m) × Bits (nL + ℓ)) (Bits (nL + ℓ + r + m)) ℂ :=
  fun p s =>
    if p.2 = dec (rightPart s) ∧
        p.1 = Fin.append (xorB (leftPart s) (π (Fin.append p.2 (zeros r))))
          (xorB (rightPart s) (g p.2)) then
      (if f p.2 then -1 else 1)
    else 0

/-- **`Π^Good_{BCD} := |e⟩⟨e|_{BC} ⊗ Σ_{x,y} |x∥y⟩⟨x∥y|_D`**, Eq. (126), p.43 (the sum over `x ∈ {0,1}^{nL}`,
`y ∈ {0,1}^ℓ` is the identity on `D`). -/
def piGood (e : Bits (nL + ℓ + r + m)) :
    Matrix (Bits (nL + ℓ + r + m) × Bits (nL + ℓ)) (Bits (nL + ℓ + r + m) × Bits (nL + ℓ)) ℂ :=
  Matrix.diagonal fun p => if p.1 = e then 1 else 0

end Raw

/-- **Ingredients of Construction 7.2.** Hsieh, Yamada, arXiv:2609.38986 (sha256 6901b59d…), p.41:
an `(nL + ℓ, m)` PRFC (`prfc`); a keyed function `f_k : {0,1}^{nL+ℓ} → {0,1}` (the PRF `F`); keyed
permutations `π_{k′}` of `{0,1}^{nL+ℓ+r}` (the PRP `Π`); and GraphSample / Recover. GraphSample is given
by its coins: `gs T n ρ` is the graph on `[2n]` sampled from `ρ ∈ {0,1}^{gc(n)}` at radius `T`, and
`recv T n G e` is `Recover(G, e)` at radius `T` (the radius is the scheme parameter `W`). -/
structure C72 where
  nL : ℕ → ℕ
  ℓ : ℕ → ℕ
  r : ℕ → ℕ
  m : ℕ → ℕ
  prfc : PRFC (fun lam => nL lam + ℓ lam) m
  f : ∀ lam, Bits lam → Bits (nL lam + ℓ lam) → Bool
  perm : ∀ lam, Bits lam → Equiv.Perm (Bits (nL lam + ℓ lam + r lam))
  gc : ℕ → ℕ
  gs : ℕ → ∀ n, Bits (gc n) → SimpleGraph (Fin (2 * n))
  recv : ℕ → ∀ n, SimpleGraph (Fin (2 * n)) → Bits (2 * n) → Bits (2 * n)

namespace C72

variable (D : C72)

/-- `nP := nL + ℓ + r + m` (p.40). -/
abbrev nP (lam : ℕ) : ℕ := D.nL lam + D.ℓ lam + D.r lam + D.m lam

/-- A graph on `[2⌊N/2⌋]` viewed on `[N]` (the last vertex is isolated when `N` is odd). -/
def embedGraph {N : ℕ} (G : SimpleGraph (Fin (2 * (N / 2)))) : SimpleGraph (Fin N) :=
  SimpleGraph.fromRel fun i j =>
    ∃ (hi : i.val < 2 * (N / 2)) (hj : j.val < 2 * (N / 2)), G.Adj ⟨i.val, hi⟩ ⟨j.val, hj⟩

/-- The first `2⌊N/2⌋` bits of an `N`-bit string. -/
def restrictEven {N : ℕ} (e : Bits N) : Bits (2 * (N / 2)) := fun i => e ⟨i.val, by omega⟩

/-- A `2⌊N/2⌋`-bit string padded with `0` to `N` bits. -/
def padEven {N : ℕ} (u : Bits (2 * (N / 2))) : Bits N :=
  fun i => if h : i.val < 2 * (N / 2) then u ⟨i.val, h⟩ else false

/-- **Secret key of Construction 7.2**, p.41: `sk = (sk′, k, k′, G, P)` with `sk′` a PRFC key,
`k, k′ ∈ {0,1}^λ`, `G` a graph on `[2⌊nP/2⌋]` (GraphSample on `1^{nP/2}`) and `P ∈ P_{nP}`. -/
def Key (lam _W : ℕ) : Type :=
  D.prfc.Key lam × Bits lam × Bits lam × SimpleGraph (Fin (2 * (D.nP lam / 2))) × PauliIdx (D.nP lam)

/-- Number of KeyGen coins: those of `PRFC.KeyGen`, `k`, `k′`, GraphSample, and `2 + 2nP` for `P`. -/
def kc (lam : ℕ) : ℕ := D.prfc.kc lam + lam + lam + D.gc (D.nP lam / 2) + (2 + D.nP lam + D.nP lam)

/-- **KeyGen of Construction 7.2**, p.41: "Run `sk′ ← PRFC.KeyGen(1^λ)` and choose `k, k′ ← {0,1}^λ`. Run
`G ← GraphSample(1^{nP/2})`. Choose `P ← P_{nP}`. Output `sk := (sk′, k, k′, G, P)`." The coins are split
in this order; the Pauli index is `(i^{2b₀+b₁}, x, z)` from its `2 + 2nP` coins, a uniform element of
`P_{nP}`. -/
def keyGen (lam W : ℕ) (ρ : Bits (D.kc lam)) : D.Key lam W :=
  let a := leftPart ρ
  let q : Bits (2 + D.nP lam + D.nP lam) := rightPart ρ
  (D.prfc.keyGen lam (leftPart (leftPart (leftPart a))),
    rightPart (leftPart (leftPart a)),
    rightPart (leftPart a),
    D.gs W (D.nP lam / 2) (rightPart a),
    (⟨2 * (if q (Fin.castAdd _ (Fin.castAdd _ (0 : Fin 2))) then 1 else 0) +
        (if q (Fin.castAdd _ (Fin.castAdd _ (1 : Fin 2))) then 1 else 0), by split_ifs <;> omega⟩,
      rightPart (leftPart q), rightPart q))

/-- **The encoding isometry** `Enc_sk = (P U_G)_{BC} ∘ V_{sk_in}`, Eq. (110), p.41, with
`f = f_k`, `π = π_{k′}`, `g = PRFC.Enc(sk′, ·)`. -/
noncomputable def encIso (lam W : ℕ) (sk : D.Key lam W) :
    Matrix (Bits (D.nP lam)) (Bits (D.nL lam)) ℂ := by
  classical
  exact pauliOp sk.2.2.2.2 * graphUnitary (embedGraph sk.2.2.2.1) *
    vSkin (D.f lam sk.2.1) (D.perm lam sk.2.2.1) (D.prfc.enc lam sk.1)

/-- **Dec of Construction 7.2**, p.41–42: 1. apply `U_G† P†` to `BC`; 2. apply `BitDec_{sk_in}`;
3. `PhaseDec`: (a) measure `BC` to get `e`, (b) run `u := Recover(G, e)`, (c) apply
`|z⟩_D ↦ (−1)^{u·(π_{k′}(z∥0^r)∥g_{sk′}(z))} |z⟩_D`, (d) output the first `nL` qubits of `D`.
As a channel: `Dec(ρ) = Σ_{e, y} K_{e,y} ρ K_{e,y}†`, where `y` runs over the traced last `ℓ` qubits of `D`.

**Formalization Note.** For odd `nP` the graph lives on the first `2⌊nP/2⌋` vertices, Recover reads
the first `2⌊nP/2⌋` bits of `e`, and `u` is padded with `0`; the paper's construction takes `nP` even. -/
noncomputable def decCh (lam W : ℕ) (sk : D.Key lam W) :
    Superop (Bits (D.nP lam)) (Bits (D.nL lam)) := by
  classical
  exact fun ρ =>
    let Gf := embedGraph (N := D.nP lam) sk.2.2.2.1
    let Wm := bitDec (D.f lam sk.2.1) (D.perm lam sk.2.2.1) (D.prfc.enc lam sk.1) (D.prfc.dec lam sk.1) *
      ((graphUnitary Gf)ᴴ * (pauliOp sk.2.2.2.2)ᴴ)
    ∑ e : Bits (D.nP lam), ∑ y : Bits (D.ℓ lam),
      let u : Bits (D.nP lam) := padEven (D.recv W (D.nP lam / 2) sk.2.2.2.1 (restrictEven e))
      let K : Matrix (Bits (D.nL lam)) (Bits (D.nP lam)) ℂ := fun a s =>
        (if dotB u (cwVec (D.perm lam sk.2.2.1) (D.prfc.enc lam sk.1) (Fin.append a y)) then -1 else 1) *
          Wm (e, Fin.append a y) s
      K * ρ * Kᴴ

/-- **Construction 7.2 (PRIC)** as a channel-level scheme from `nL` to `nP` qubits. -/
noncomputable def scheme : ChScheme D.nL D.nP where
  Key := D.Key
  kc := D.kc
  keyGen := D.keyGen
  enc lam W sk := conjMap (D.encIso lam W sk)
  dec := D.decCh

end C72

end QuantumPRC


