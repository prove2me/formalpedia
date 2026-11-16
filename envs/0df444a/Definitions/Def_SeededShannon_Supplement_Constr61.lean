-- Prove2me | Definitions.Def_SeededShannon_Supplement_Constr61
-- name    : SeededShannon_Supplement_Constr61
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:38:09.547448+00:00
-- url     : https://prove2.me/theorems/b8a839d6-1a6a-46a4-92f7-b77633598091
-- title:
--   Construction 6.1 (seeded code): Derive, EncodeProg, DecodeProg, Setup and the validity conditions
-- statement:
--   **Construction 6.1** builds a seeded code from an indistinguishability obfuscator $i\mathcal O$, a single point binding hash $\Pi_{\mathrm{SPH}}$, a puncturable PRF $\Pi_{\mathrm{PPRF}}$, a puncturable $\tau$-robust PRC $\Pi_{\mathrm{PPRC}}$, a sparse-set obfuscator $\Pi_{\mathrm{EvObf}_s}$, a partition obfuscator $\Pi_{\mathrm{EvObf}_p}$ and a balanced code $\Pi_{\mathrm{code}}$.
--
--   *Lengths (6.1).* $\ell_{\mathrm{hash}}$ is the hash length, $\ell$ the PPRC output length on $\ell_{\mathrm{hash}}$-bit inputs, $D=\mathrm{lcm}(b,\ell)$,
--   $$N=D\cdot\Big\lceil\frac{k}{R\cdot D}\Big\rceil,\qquad t=N/\ell,\qquad m=N/b,$$
--   $\ell_F=r_s+r_p+N$, and the list bound of Lemma 6.2 is $L=t\cdot L_{\mathrm{pprc}}(\lambda,\ell_{\mathrm{hash}})\cdot L_{\mathrm{bal}}(N)$. Supported lengths are $k_{\min}(\lambda)\le k\le 2^\lambda$.
--
--   *Derive (Fig. 6).* Parse $\Pi_{\mathrm{PPRF}}.\mathrm{Eval}(K_{\mathrm{PPRF}},h)$ as $(r_s,r_p,s_h)$; run both $\mathrm{GenProg}$ algorithms on these tapes; read $S_h$ and $P_h$ off the returned seeds; order the blocks of $P_h$ by least element and set $\pi_h((j-1)b+r)=a_{j,r}$, with $(\pi_h(v))_{\pi_h(a)}=v_a$.
--
--   *EncodeProg (Fig. 7).* $h=\mathrm{Hash}(hk,x)$, $c=\pi_h(\mathrm{Encode}(\mathrm{pad}(x)))\oplus s_h$, and chunk $i\in S_h$ is replaced by $\Pi_{\mathrm{PPRC}}.\mathrm{Eval}(K^{(i)},h)$.
--
--   *DecodeProg (Fig. 8).* Collect $H=\bigcup_i\Pi_{\mathrm{PPRC}}.\mathrm{Recover}(K^{(i)},y_i)$; for each $h\in H$ list-decode $\pi_h^{-1}(y\oplus s_h)$; keep a candidate $x$ if its padding is zero, $\mathrm{Hash}(hk,x)=h$, $e=y\oplus\mathrm{EncodeProg}(x)$ has $\mathrm{wt}(e)\le pN$, and both predicate programs reject ($w(e)$ marks the chunks with more than $\tau\ell$ errors); return the survivors sorted and without duplicates.
--
--   *Setup.* Sample $hk\leftarrow\Pi_{\mathrm{SPH}}.\mathrm{Setup}(1^\lambda,0^k)$, $K_{\mathrm{PPRF}}$ and $K^{(1)},\dots,K^{(t)}$; obfuscate circuits for EncodeProg and DecodeProg, padded to sizes $S_E,S_D$, the decoder's output having room for $L+1$ candidates; output $\mathrm{crs}=(\lambda,k,N,\tilde P_{\mathrm{Enc}},\tilde P_{\mathrm{Dec}})$. Encode and Decode evaluate $\tilde P_{\mathrm{Enc}}$ and $\tilde P_{\mathrm{Dec}}$.
--
--   *Validity.* The data are valid when $0<p<1/2$, $0<\varepsilon<1-H(p)$, $1-H(p)-\varepsilon/2<R<1-H(p)$, $p<\tau<1/2$, $0<\gamma<p/\tau$, $R<1-H(\tau)-C\sqrt\gamma$; every primitive satisfies its definition (the PPRC recovery lists are bounded by $L_{\mathrm{pprc}}$; $\Pi_{\mathrm{EvObf}_s}$ at density $p/\tau$ with $B_s\le C_s t^{3/4}$; $\Pi_{\mathrm{EvObf}_p}$ at $(p,\tau,\gamma/2,b)$; $\Pi_{\mathrm{code}}$ with the guarantees of Theorem 3.14 at $\zeta=C\sqrt\gamma$); $r_s,r_p$ bound the random tapes; and $k_{\min}$ is a polynomial such that every supported $k$ meets the length requirements and (6.2): $b\,B_s(\lambda,t)/t\le\gamma/2$ and $D/k\le\varepsilon/2$.
--
--   The predicate $\mathrm{Ingredients61}$ asserts that the primitives exist for every choice of parameters the construction may need (Theorem 7.15's hypothesis).
--
--   **Formalization Note** Circuits for the two programs are supplied by *circuit builders*: polynomial-time maps from the keys to circuits of the padded sizes that compute the programs exactly. "Puncturable" is $1$-puncturable. Each $\mathrm{GenProg}$ reads the first $\mathrm{progCoins}$ bits of its tape ("padding unused random bits"). The constant $C$ is a parameter with a balanced code of rate $1-H(\tau)-C\sqrt\gamma$.
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Construction 6.1, pp.37–38 (PDF pp.40–41); Figs. 6–8, pp.39–40 (PDF pp.42–43); Lemma 6.2, p.40

import Mathlib
import Definitions.Def_NoisyOWMPC_IOScheme
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_SeededShannon_SeededCode
import Definitions.Def_SeededShannon_PPRF
import Definitions.Def_SeededShannon_SPH
import Definitions.Def_SeededShannon_PPRC
import Definitions.Def_SeededShannon_Supplement_parseTup
import Definitions.Def_SeededShannon_Supplement_BalCodeFamily
import Definitions.Def_SeededShannon_Supplement_SparseSetObf

set_option autoImplicit false

namespace SeededShannon.Supplement

open LaconicBarrier NoisyOWMPC SeededShannon

/-- The constants and ingredients of **Construction 6.1 (Seeded Code)** (Dujmovic, Lu, Silbak,
Wichs, *Shannon Rate Seeded Codes from Indistinguishability Obfuscation*, STOC 2027 submission
(manuscript sha256 52f4b606…a769709), Construction 6.1, pp.37–38): the target radius `p` and slack
`ε`, the rational rate `R`, the constants `τ`, `γ`, the constant `C` of the balanced code, the block
size `b`; the obfuscator `iO`, the single point binding hash `Π_SPH`, the puncturable PRF `Π_PPRF`,
the puncturable PRC `Π_PPRC` with a bound `L_pprc(λ, ℓhash)` on one recovery list, the sparse-set
obfuscator `Π_EvObf_s` (minimum length `N_min,s`, set-size bound `B_s ≤ C_s · t^{3/4}`, seed map
`setOf`), the partition obfuscator `Π_EvObf_p` (minimum length `N_min,p`, seed map `partOf`), the
balanced code `Π_code` (valid from length `n₀`), the minimum message length `k_min` and the
random-tape bounds `r_s(λ, t)`, `r_p(λ, N)` of the two `GenProg` algorithms.

**Formalization Note** The conditions the paper places on these data are `Constr61.Valid`. -/
structure Constr61 where
  /-- the error radius `p` -/
  p : ℝ
  /-- the rate slack `ε` -/
  ε : ℝ
  /-- the rational rate `R` -/
  R : ℚ
  /-- the per-chunk radius `τ` -/
  τ : ℝ
  /-- the imbalance `γ` -/
  γ : ℝ
  /-- the constant `C` of Theorem 3.14 -/
  Cbal : ℝ
  /-- the block size `b` -/
  b : ℕ
  /-- the obfuscator `iO` -/
  iO : IOScheme
  /-- the single point binding hash `Π_SPH` -/
  sph : SPH
  /-- the puncturable PRF `Π_PPRF` -/
  prf : PPRF
  /-- the puncturable PRC `Π_PPRC` -/
  prc : PPRC
  /-- `L_pprc(λ, ℓhash)`, a bound on one PPRC recovery list -/
  Lpprc : ℕ → ℕ
  /-- the sparse-set obfuscator `Π_EvObf_s` -/
  evs : EvObf
  /-- its minimum input length -/
  NminS : ℕ → ℕ
  /-- its set-size bound `B_s(λ, t)` -/
  Bs : ℕ → ℕ → ℕ
  /-- the constant `C_s` of `B_s ≤ C_s · t^{3/4}` -/
  Cs : ℝ
  /-- its map from sampling seeds to sets (Theorem 5.2) -/
  setOf : ℕ → ℕ → List Bool → List Bool
  /-- the partition obfuscator `Π_EvObf_p` -/
  evp : EvObf
  /-- its minimum input length -/
  NminP : ℕ → ℕ
  /-- its map from sampling seeds to partition codes (Theorem 5.3) -/
  partOf : ℕ → ℕ → List Bool → List Bool
  /-- the balanced code `Π_code` -/
  code : BalCodeFamily
  /-- the length from which `Π_code` has its guarantees -/
  n₀ : ℕ
  /-- the minimum message length `k_min(λ)` -/
  kmin : ℕ → ℕ
  /-- the random-tape bound `r_s(λ, t)` of `Π_EvObf_s.GenProg` -/
  rs : ℕ → ℕ → ℕ
  /-- the random-tape bound `r_p(λ, N)` of `Π_EvObf_p.GenProg` -/
  rp : ℕ → ℕ → ℕ

namespace Constr61

variable (X : Constr61)

/-- `ℓhash(λ)`, the output length of `Π_SPH`. -/
def lh (lam : ℕ) : ℕ := X.sph.hlen lam

/-- `ℓ(λ)`, the output length of `Π_PPRC` on `ℓhash`-bit inputs (the chunk length). -/
def lc (lam : ℕ) : ℕ := X.prc.lout lam (X.lh lam)

/-- `D = lcm(b, ℓ)` (6.1). -/
def Dl (lam : ℕ) : ℕ := Nat.lcm X.b (X.lc lam)

/-- The codeword length `N = D · ⌈k/(R · D)⌉` (6.1). -/
def Nl (lam k : ℕ) : ℕ := X.Dl lam * (⌈(k : ℚ) / (X.R * X.Dl lam)⌉).toNat

/-- The number of chunks `t = N/ℓ` (6.1). -/
def tl (lam k : ℕ) : ℕ := X.Nl lam k / X.lc lam

/-- The PRF output length `ℓ_F = r_s + r_p + N` (p.38). -/
def lF (lam k : ℕ) : ℕ := X.rs lam (X.tl lam k) + X.rp lam (X.Nl lam k) + X.Nl lam k

/-- The list bound `L = t · L_pprc(λ, ℓhash) · L_bal(N)` of Lemma 6.2 (p.40). -/
def Llist (lam k : ℕ) : ℕ := X.tl lam k * X.Lpprc lam * X.code.Lbal (X.Nl lam k)

/-- The supported message lengths `k_min(λ) ≤ k ≤ 2^λ` (p.38). -/
def supp (lam k : ℕ) : Prop := X.kmin lam ≤ k ∧ k ≤ 2 ^ lam

end Constr61

/-- The partition `P_σ` read from its code `partOf(σ) = partCode P_σ` (Theorem 5.3's deterministic
map; Fig. 6, step 2), as a block labelling of `[n]`.

**Formalization Note** `partCode` is injective on block labellings, so the partition is unique; it
is selected by choice (the all-zero labelling for a code of no partition). -/
noncomputable def partDecode (b n : ℕ) (s : List Bool) : Fin n → ℕ := by
  classical
  exact if h : ∃ P : Fin n → ℕ, IsBlockPartition b n P ∧ partCode P = s then Classical.choose h
    else fun _ => 0

/-- The position in the consecutive-block layout of the position `a`, for the permutation `π_P`
of Fig. 6, step 3: order the blocks of `P` by their least elements and write the `j`-th block
(from `0`) as `{a_{j,0} < ⋯ < a_{j,b−1}}`; then `π_P(j · b + r) = a_{j,r}`, and
`consecIdx b P (a_{j,r}) = j · b + r`. The block index `j` of `a` is the number of block leaders
(least elements) below the least element of the block of `a`, and `r` is the number of elements of
that block below `a`. -/
noncomputable def consecIdx {n : ℕ} (b : ℕ) (P : Fin n → ℕ) (a : Fin n) : ℕ := by
  classical
  exact b * (Finset.univ.filter (fun i : Fin n =>
      (∀ j : Fin n, P j = P i → i ≤ j) ∧ ∀ j : Fin n, P j = P a → i < j)).card +
    (Finset.univ.filter (fun i : Fin n => P i = P a ∧ i < a)).card

/-- `π_P(v)` with the convention of Fig. 6, `(π_P(v))_{π_P(c)} = v_c`: position `a` of `π_P(v)`
carries `v_{π_P^{−1}(a)}`, the bit of `v` at the consecutive position of `a`. -/
noncomputable def permApply {n : ℕ} (b : ℕ) (P : Fin n → ℕ) (v : Fin n → Bool) : Fin n → Bool :=
  fun a => if h : consecIdx b P a < n then v ⟨consecIdx b P a, h⟩ else false

/-- `π_P^{−1}(w)`: position `c` carries `w_{π_P(c)}`, the bit of `w` at the position whose
consecutive position is `c`. -/
noncomputable def permInv {n : ℕ} (b : ℕ) (P : Fin n → ℕ) (w : Fin n → Bool) : Fin n → Bool := by
  classical
  exact fun c => decide (∃ a : Fin n, consecIdx b P a = c.val ∧ w a = true)

/-- `pad(x)`: a message `x ∈ {0,1}^k` padded with zeros to `k_bal` bits (p.38). -/
def padTo (kb : ℕ) (x : List Bool) : Fin kb → Bool := fun j => x.getD j.val false

/-- The keys hard-coded into the programs of Figs. 7 and 8: `hk_SPH`, `K_PPRF` and the chunk keys
`(K_PPRC^{(i)})_{i ∈ [t]}` (in order). -/
structure Keys61 where
  /-- `hk_SPH` -/
  hk : List Bool
  /-- `K_PPRF` -/
  kprf : List Bool
  /-- `K_PPRC^{(1)}, …, K_PPRC^{(t)}` -/
  kprc : List (List Bool)

/-- The bit-string code of the keys (input of the circuit builders). -/
def Keys61.code (K : Keys61) : List Bool :=
  QAdvFew.PoQOracle.tup [K.hk, K.kprf, QAdvFew.PoQOracle.tup K.kprc]

/-- The output of **`Derive_{K_PPRF}(h)`** (Fig. 6, p.39): the set `S_h ⊆ [t]` (indicator vector),
the partition `P_h` of `[N]` (block labelling), the mask `s_h ∈ {0,1}^N`, and the two predicate
programs `P̃_{s,h}`, `P̃_{p,h}`; the permutation `π_h` is `permApply b P_h`. -/
structure Derived61 (t N : ℕ) where
  /-- `S_h` -/
  S : Fin t → Bool
  /-- `P_h` -/
  P : Fin N → ℕ
  /-- `s_h` -/
  s : Fin N → Bool
  /-- `P̃_{s,h}` -/
  progS : List Bool
  /-- `P̃_{p,h}` -/
  progP : List Bool

namespace Constr61

variable (X : Constr61)

/-- **`Derive_{K_PPRF}(h)`** (Fig. 6, p.39): (1) parse `Π_PPRF.Eval(K_PPRF, h)` as `(r_s, r_p, s_h)` of
lengths `r_s, r_p, N`; (2) run `(σ_{s,h}, P̃_{s,h}) ← Π_EvObf_s.GenProg(1^λ, 1^t; r_s)` and
`(σ_{p,h}, P̃_{p,h}) ← Π_EvObf_p.GenProg(1^λ, 1^N; r_p)`, and compute `S_h = S_{σ_{s,h}}`,
`P_h = P_{σ_{p,h}}` with the deterministic maps of Theorems 5.2 and 5.3; (3) `π_h` from the blocks
of `P_h` ordered by least elements.

**Formalization Note** "Padding unused random bits" (p.38): each `GenProg` reads the first
`progCoins` bits of its tape of length `r_s` (resp. `r_p`); `Valid` requires `progCoins ≤ r_s`
(resp. `≤ r_p`) at supported lengths. Bits beyond the end of a too-short PRF output read `0`. -/
noncomputable def derive (lam k : ℕ) (kprf h : List Bool) : Derived61 (X.tl lam k) (X.Nl lam k) :=
  let z := (X.prf.eval kprf h).getD []
  let rS := z.take (X.rs lam (X.tl lam k))
  let rP := (z.drop (X.rs lam (X.tl lam k))).take (X.rp lam (X.Nl lam k))
  let sh := z.drop (X.rs lam (X.tl lam k) + X.rp lam (X.Nl lam k))
  let gS := X.evs.genProg lam (X.tl lam k) (fun j => rS.getD j.val false)
  let gP := X.evp.genProg lam (X.Nl lam k) (fun j => rP.getD j.val false)
  { S := fun i => (X.setOf lam (X.tl lam k) gS.1).getD i.val false
    P := partDecode X.b (X.Nl lam k) (X.partOf lam (X.Nl lam k) gP.1)
    s := fun i => sh.getD i.val false
    progS := gS.2
    progP := gP.2 }

/-- **Program `EncodeProg`** (Fig. 7, p.39) with the keys `K` hard-coded, on `x ∈ {0,1}^k`:
(1) `h = Π_SPH.Hash(hk_SPH, x)` and `v = Π_code.Encode(pad(x))`; (2) derive
`(S_h, P_h, π_h, s_h, …)` and set `c = π_h(v) ⊕ s_h`; (3) parse `c` into `t` consecutive `ℓ`-bit chunks
and, for each `i ∈ S_h`, replace chunk `c_i` by `Π_PPRC.Eval(K_PPRC^{(i)}, h)`; (4) return `c`.

**Formalization Note** Chunks and positions are indexed from `0`: chunk `i` holds positions
`iℓ, …, iℓ + ℓ − 1`. -/
noncomputable def encodeProg (lam k : ℕ) (K : Keys61) (x : List Bool) : List Bool :=
  let N := X.Nl lam k
  let h := X.sph.hash K.hk x
  let v := X.code.enc N (padTo (X.code.kbal N) x)
  let d := X.derive lam k K.kprf h
  let c0 : Fin N → Bool := fun a => xor (permApply X.b d.P v a) (d.s a)
  bits (fun a : Fin N =>
    if hi : a.val / X.lc lam < X.tl lam k then
      (if d.S ⟨a.val / X.lc lam, hi⟩ then
        ((X.prc.eval (K.kprc.getD (a.val / X.lc lam) []) h).getD []).getD (a.val % X.lc lam) false
       else c0 a)
    else c0 a)

/-- The heavy-chunk indicator `w(e) ∈ {0,1}^t` of Fig. 8, step 2(c): `w_i(e) = 1 ⟺ wt(e_i) > τ · ℓ`,
with `e_i` the `i`-th `ℓ`-bit chunk of `e`. -/
noncomputable def heavy (lam k : ℕ) (e : Fin (X.Nl lam k) → Bool) : Fin (X.tl lam k) → Bool := by
  classical
  exact fun i => decide (X.τ * X.lc lam <
    ((Finset.univ.filter (fun a : Fin (X.Nl lam k) => a.val / X.lc lam = i.val ∧ e a = true)).card
      : ℝ))

open Classical in
/-- **Program `DecodeProg`** (Fig. 8, p.40) with the keys `K` hard-coded, on `y ∈ {0,1}^N`:
(1) parse `y` into `ℓ`-bit chunks and compute `H = ⋃_{i ∈ [t]} Π_PPRC.Recover(K_PPRC^{(i)}, y_i)`;
(2) for each `h ∈ H`, derive `(S_h, P_h, π_h, s_h, P̃_{s,h}, P̃_{p,h})` and list-decode
`T′_h = Π_code.ListDec(π_h^{−1}(y ⊕ s_h))`; keep a candidate when (a) all its bits after position
`k` are zero and, for its first `k` bits `x`, `Π_SPH.Hash(hk_SPH, x) = h`; (b) `e = y ⊕ EncodeProg(x)`
has `wt(e) ≤ p · N`; (c) `Π_EvObf_s.Eval(P̃_{s,h}, w(e)) = 0` and `Π_EvObf_p.Eval(P̃_{p,h}, e) = 0`;
(3) return the kept messages in lexicographic order, without duplicates.

**Formalization Note** `EncodeProg` is called unobfuscated with the same keys, as in Fig. 8.
Candidates have length `k_bal(N)` by their type. -/
noncomputable def decodeProg (lam k : ℕ) (K : Keys61) (y : List Bool) : List (List Bool) :=
  let N := X.Nl lam k
  let ℓ := X.lc lam
  let yv : Fin N → Bool := fun a => y.getD a.val false
  let H := (List.range (X.tl lam k)).flatMap
    (fun i => X.prc.recover (K.kprc.getD i []) ((y.drop (i * ℓ)).take ℓ))
  let T := H.flatMap (fun h =>
    let d := X.derive lam k K.kprf h
    (X.code.dec N (permInv X.b d.P (fun a => xor (yv a) (d.s a)))).filterMap (fun u =>
      let x := (List.ofFn u).take k
      let e : Fin N → Bool := fun a => xor (yv a) ((X.encodeProg lam k K x).getD a.val false)
      if (∀ j : Fin (X.code.kbal N), k ≤ j.val → u j = false) ∧ X.sph.hash K.hk x = h ∧
          (wt e : ℝ) ≤ X.p * N ∧ X.evs.eval d.progS (bits (X.heavy lam k e)) = false ∧
          X.evp.eval d.progP (bits e) = false
      then some x else none))
  T.dedup.mergeSort (fun a b => decide (a ≤ b))

/-- The coins of `Π_SPH.Setup(1^λ, 0^k)`, of `Π_PPRF.KeyGen(1^λ, 1^{ℓhash}, 1^{ℓ_F})` and of one
`Π_PPRC.KeyGen(1^λ, 1^{ℓhash})`, and their total over the keys of Setup (`t` PPRC keys). -/
def keyCoins (lam k : ℕ) : ℕ :=
  X.sph.coins lam k + X.prf.keyCoins lam (X.lh lam) (X.lF lam k) +
    X.tl lam k * X.prc.keyCoins lam (X.lh lam)

/-- The keys sampled by Setup (p.38) from key coins `r`:
`hk_SPH ← Π_SPH.Setup(1^λ, 0^k)`, `K_PPRF ← Π_PPRF.KeyGen(1^λ, 1^{ℓhash}, 1^{ℓ_F})`,
`K_PPRC^{(i)} ← Π_PPRC.KeyGen(1^λ, 1^{ℓhash})` for `i ∈ [t]`, on consecutive slices of `r`. -/
def keysOf (lam k : ℕ) (r : Fin (X.keyCoins lam k) → Bool) : Keys61 :=
  let c1 := X.sph.coins lam k
  let c2 := X.prf.keyCoins lam (X.lh lam) (X.lF lam k)
  let c3 := X.prc.keyCoins lam (X.lh lam)
  { hk := X.sph.setup lam k (fun _ => false) (slice r 0 c1)
    kprf := X.prf.keyGen lam (X.lh lam) (X.lF lam k) (slice r c1 c2)
    kprc := (List.range (X.tl lam k)).map (fun i => X.prc.keyGen lam (X.lh lam)
      (slice r (c1 + c2 + i * c3) c3)) }

end Constr61

/-- The padded output representation of a decoder circuit (p.38: "padded to common polynomial size
and output-length bounds … the padded decoder output has room for one extra candidate"): `slots`
blocks of `k + 1` bits; block `j` is `1x` for the `j`-th listed message `x` (its first `k` bits) and
`0^{k+1}` when the list has fewer than `j + 1` entries. -/
def listOut (slots k : ℕ) (T : List (List Bool)) : List Bool :=
  (List.range slots).flatMap (fun j => match T[j]? with
    | some x => true :: List.ofFn (fun i : Fin k => x.getD i.val false)
    | none => false :: List.replicate k false)

/-- Reading the padded output representation: the messages of the blocks of `k + 1` bits whose
flag bit is `1`, in order. -/
def parseListOut (k : ℕ) (o : List Bool) : List (List Bool) :=
  (List.range (o.length / (k + 1))).filterMap (fun j =>
    let blk := (o.drop (j * (k + 1))).take (k + 1)
    if blk.headD false then some (blk.drop 1) else none)

/-- **Circuit builders** for Construction 6.1: for keys `K` at `(λ, k)`, a circuit with `k` inputs
for `EncodeProg` and one with `N` inputs for `DecodeProg`, of the padded sizes `S_E(λ, k)`,
`S_D(λ, k)` (p.38: "Obfuscate the programs in Figs. 7 and 8, with these keys and the public
parameters hardcoded … Encoders and decoders are padded to common polynomial size"). -/
structure Builders61 (X : Constr61) where
  /-- the padded encoder size `S_E(λ, k)` -/
  SE : ℕ → ℕ → ℕ
  /-- the padded decoder size `S_D(λ, k)` -/
  SD : ℕ → ℕ → ℕ
  /-- the encoder circuit -/
  encCirc : (lam k : ℕ) → Keys61 → MCircuit k
  /-- the decoder circuit -/
  decCirc : (lam k : ℕ) → Keys61 → MCircuit (X.Nl lam k)

namespace Builders61

variable {X : Constr61} (B : Builders61 X)

/-- The builders are **valid at size thresholds `S₀_E`, `S₀_D`**: polynomial padded sizes at least
the thresholds; on every key choice of Setup at every supported `(λ, k)`, the encoder circuit has
size exactly `S_E(λ, k)` and computes `EncodeProg` on every `x ∈ {0,1}^k`, the decoder circuit has
size exactly `S_D(λ, k)` and outputs the padded representation (`L + 1` slots) of `DecodeProg(y)` on
every `y ∈ {0,1}^N`; and one polynomial-time machine computes both circuit descriptions from
`(1^λ, 1^k, K)`. -/
def Valid (S0E S0D : ℕ → ℕ → ℕ) : Prop :=
  PolyBounded₂ B.SE ∧ PolyBounded₂ B.SD ∧
  (∀ lam k, X.supp lam k →
    S0E lam k ≤ B.SE lam k ∧ S0D lam k ≤ B.SD lam k ∧
    ∀ r : Fin (X.keyCoins lam k) → Bool,
      (B.encCirc lam k (X.keysOf lam k r)).size = B.SE lam k ∧
      (B.decCirc lam k (X.keysOf lam k r)).size = B.SD lam k ∧
      (∀ x : Fin k → Bool, (B.encCirc lam k (X.keysOf lam k r)).eval (bits x) =
        X.encodeProg lam k (X.keysOf lam k r) (bits x)) ∧
      ∀ y : Fin (X.Nl lam k) → Bool, (B.decCirc lam k (X.keysOf lam k r)).eval (bits y) =
        listOut (X.Llist lam k + 1) k (X.decodeProg lam k (X.keysOf lam k r) (bits y))) ∧
  PolyTimeOn (ι := (z : {z : ℕ × ℕ // X.supp z.1 z.2}) × (Fin (X.keyCoins z.1.1 z.1.2) → Bool))
    (fun i => [unary i.1.1.1, unary i.1.1.2, (X.keysOf i.1.1.1 i.1.1.2 i.2).code])
    (fun i => QAdvFew.PoQOracle.tup [(B.encCirc i.1.1.1 i.1.1.2 (X.keysOf i.1.1.1 i.1.1.2 i.2)).code,
      (B.decCirc i.1.1.1 i.1.1.2 (X.keysOf i.1.1.1 i.1.1.2 i.2)).code])

/-- The number of coins of Setup: the key coins, then the coins of the two obfuscations. -/
def setupCoins (lam k : ℕ) : ℕ :=
  X.keyCoins lam k + X.iO.coins lam k (B.SE lam k) + X.iO.coins lam (X.Nl lam k) (B.SD lam k)

/-- **Setup(1^λ, 1^k)** of Construction 6.1 (p.38): sample the keys, obfuscate the circuits of
`EncodeProg` and `DecodeProg` with the keys hard-coded, `P̃_Enc ← iO(1^λ, C_Enc)`,
`P̃_Dec ← iO(1^λ, C_Dec)`, and output `crs = (λ, k, N, P̃_Enc, P̃_Dec)`. -/
noncomputable def setup (lam k : ℕ) (r : Fin (B.setupCoins lam k) → Bool) : List Bool :=
  let c0 := X.keyCoins lam k
  let K := X.keysOf lam k (slice r 0 c0)
  let cE := X.iO.coins lam k (B.SE lam k)
  let cD := X.iO.coins lam (X.Nl lam k) (B.SD lam k)
  let PE := X.iO.obf lam k (B.SE lam k) (B.encCirc lam k K) (slice r c0 cE)
  let PD := X.iO.obf lam (X.Nl lam k) (B.SD lam k) (B.decCirc lam k K) (slice r (c0 + cE) cD)
  QAdvFew.PoQOracle.tup [unary lam, unary k, unary (X.Nl lam k), PE.code, PD.code]

/-- **The seeded code of Construction 6.1** (p.38): `Setup` as above; `Encode(crs, x)` returns
`P̃_Enc(x)` for `x ∈ {0,1}^k`; `Decode(crs, y)` returns the list output by `P̃_Dec(y)` for
`y ∈ {0,1}^N`. Malformed inputs give the empty output (p.22). -/
noncomputable def code61 : SeededCode where
  N := X.Nl
  setupCoins := B.setupCoins
  setup := B.setup
  encode := fun crs x =>
    match circOf (tupGet crs 1).length (tupGet crs 3) with
    | some C => if x.length = (tupGet crs 1).length then C.eval x else []
    | none => []
  decode := fun crs y =>
    match circOf (tupGet crs 2).length (tupGet crs 4) with
    | some C => if y.length = (tupGet crs 2).length then
        parseListOut (tupGet crs 1).length (C.eval y) else []
    | none => []

end Builders61

namespace Constr61

variable (X : Constr61)

/-- **The primitives and constants of Construction 6.1 satisfy their stated definitions**
(pp.37–38):
1. `0 < p < 1/2` and `0 < ε < 1 − H(p)`; `1 − H(p) − ε/2 < R < 1 − H(p)`; `p < τ < 1/2`,
   `0 < γ < p/τ`, `C > 0` and `R < 1 − H(τ) − C · √γ`;
2. `iO` is an indistinguishability obfuscator; `Π_SPH` is a single point binding hash; `Π_PPRF` is a
   puncturable PRF; `Π_PPRC` is a puncturable `τ`-robust PRC on `ℓhash`-bit inputs, and every
   recovery list under a generated key has at most `L_pprc(λ)` entries, `L_pprc` polynomial;
3. `Π_EvObf_s` is the sparse-set obfuscator of Theorem 5.2 at density `p/τ` with the parameters of
   Corollary 5.9; `Π_EvObf_p` is the partition obfuscator at `(p, τ, γ/2, b)`; `Π_code` has the
   guarantees of Theorem 3.14 at `(b, τ, γ)` with `ζ = C · √γ`;
4. `r_s`, `r_p` are polynomial bounds on the random tapes of the two `GenProg` algorithms at their
   supported lengths;
5. `k_min` is a polynomial such that, for every supported `k` (`k_min(λ) ≤ k ≤ 2^λ`), the sparse-set
   obfuscator supports length `t`, the partition obfuscator and the balanced code support length `N`,
   and (6.2) holds: `b · B_s(λ, t)/t ≤ γ/2` and `D/k ≤ ε/2`.

**Formalization Note** `H` is the binary entropy in bits. "Puncturable" is the published
`t`-puncturability with `t = 1` (the construction and its proof puncture at one point `{h*}`). The
constant `C` is a parameter, not fixed to the constant of Theorem 3.14: the construction uses it only
through the rate `1 − H(τ) − C√γ` of `Π_code`, so every `C` with a code of this rate qualifies, the
constant of Theorem 3.14 among them. The partition obfuscator supports exactly the lengths divisible
by `b`, and `b ∣ D ∣ N`. -/
def Valid : Prop :=
  (0 < X.p ∧ X.p < 1 / 2 ∧ 0 < X.ε ∧ X.ε < 1 - WildeQIT.binaryEntropy X.p) ∧
  (1 - WildeQIT.binaryEntropy X.p - X.ε / 2 < (X.R : ℝ) ∧ (X.R : ℝ) < 1 - WildeQIT.binaryEntropy X.p) ∧
  (X.p < X.τ ∧ X.τ < 1 / 2 ∧ 0 < X.γ ∧ X.γ < X.p / X.τ ∧ 0 < X.Cbal ∧
    (X.R : ℝ) < 1 - WildeQIT.binaryEntropy X.τ - X.Cbal * Real.sqrt X.γ) ∧
  X.iO.IsIO ∧ X.sph.IsSPH ∧ X.prf.IsPPRF (fun _ => 1) ∧
  X.prc.IsPPRCAt (fun _ => 1) X.τ X.sph.hlen ∧
  PolyBounded X.Lpprc ∧
  (∀ (lam : ℕ) (r : Fin (X.prc.keyCoins lam (X.lh lam)) → Bool)
      (y : Fin (X.prc.lout lam (X.lh lam)) → Bool),
    (X.prc.recover (X.prc.keyGen lam (X.lh lam) r) (bits y)).length ≤ X.Lpprc lam) ∧
  SparseSetObf (X.p / X.τ) X.NminS X.Bs X.Cs X.evs X.setOf ∧
  PartitionObf X.p X.τ (X.γ / 2) X.b X.NminP X.evp X.partOf ∧
  X.code.IsBalancedCode X.b X.τ X.γ (X.Cbal * Real.sqrt X.γ) X.n₀ ∧
  PolyBounded₂ X.rs ∧ PolyBounded₂ X.rp ∧
  (∀ lam n, X.NminS lam ≤ n → X.evs.progCoins lam n ≤ X.rs lam n) ∧
  (∀ lam n, X.NminP lam ≤ n → X.b ∣ n → X.evp.progCoins lam n ≤ X.rp lam n) ∧
  PolyBounded X.kmin ∧
  ∀ lam k, X.supp lam k →
    X.NminS lam ≤ X.tl lam k ∧ X.NminP lam ≤ X.Nl lam k ∧ X.n₀ ≤ X.Nl lam k ∧
    (X.b * X.Bs lam (X.tl lam k) : ℝ) / X.tl lam k ≤ X.γ / 2 ∧
    (X.Dl lam : ℝ) / k ≤ X.ε / 2

end Constr61

/-- **The ingredients of Construction 6.1 exist** (Theorem 7.15, p.53: "Assume the ingredients of
Construction 6.1 satisfy their stated definitions"), for every choice of the constants the
construction may need:
1. an indistinguishability obfuscator; a single point binding hash `Π_SPH`; a puncturable PRF;
2. for every `0 < τ < 1/2`, a puncturable `τ`-robust PRC on `ℓhash`-bit inputs (`ℓhash` of `Π_SPH`);
3. for every density `0 < δ < 1`, a sparse-set obfuscator of Theorem 5.2 with the parameters of
   Corollary 5.9;
4. for all `0 < p < τ < 1/2` and `0 < γ < p/τ`, and every sufficiently large block size `b`, a
   partition obfuscator at `(p, τ, γ, b)`.

**Formalization Note** The balanced code `Π_code` is not an assumption: Theorem 3.14 supplies it
unconditionally (and Theorem 7.15's proof uses the specific code of Lemma 7.5). "Puncturable" is
`1`-puncturable, as in `Constr61.Valid`. -/
def Ingredients61 : Prop :=
  (∃ O : IOScheme, O.IsIO) ∧
  ∃ H : SPH, H.IsSPH ∧ (∃ F : PPRF, F.IsPPRF (fun _ => 1)) ∧
    (∀ τ : ℝ, 0 < τ → τ < 1 / 2 → ∃ P : PPRC, P.IsPPRCAt (fun _ => 1) τ H.hlen) ∧
    (∀ δ : ℝ, 0 < δ → δ < 1 → ∃ (Nmin : ℕ → ℕ) (B : ℕ → ℕ → ℕ) (Cs : ℝ) (O : EvObf)
        (setOf : ℕ → ℕ → List Bool → List Bool), SparseSetObf δ Nmin B Cs O setOf) ∧
    ∀ p τ γ : ℝ, 0 < p → p < τ → τ < 1 / 2 → 0 < γ → γ < p / τ →
      ∃ b₀ : ℕ, ∀ b ≥ b₀, ∃ (Nmin : ℕ → ℕ) (O : EvObf) (partOf : ℕ → ℕ → List Bool → List Bool),
        PartitionObf p τ γ b Nmin O partOf

end SeededShannon.Supplement


