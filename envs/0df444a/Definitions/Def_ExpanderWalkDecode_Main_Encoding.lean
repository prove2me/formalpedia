-- Prove2me | Definitions.Def_ExpanderWalkDecode_Main_Encoding
-- name    : ExpanderWalkDecode_Main_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:23:37.437937+00:00
-- url     : https://prove2.me/theorems/785c1362-f4ce-4072-a53c-777da0625102
-- title:
--   Input and output layouts of the algorithmic statements
-- statement:
--   Each algorithmic statement runs one fixed program on an input written into the memory banks and reads its answer from the output list. Outer vertex sets are $\{0,\dots,|A|-1\}$; a port $x\in\mathbb F_2^m$ is coded by $\sum_i x_i2^i$, an inner vertex by the codes of its blocks, and a code coordinate $(a,b,j)$ by the mixed-radix number $a+|A|(\mathrm{code}(b)+2^{ms}\mathrm{code}(j))$.
--
--   The **walk structure** is written as: integer bank 0 starts with $|A|,m,s,q,t$ followed by the statement's integer parameters; integer bank 1 holds the rotation table of the outer graph; integer bank 2 the generators of the inner graph; integer bank 3 the embedding $\iota$ (when present). Real bank 0 holds the statement's real scalars ($\rho,\delta,\lambda$), real bank 1 the received word at the codes of its coordinates, real bank 2 the statement's real data. Vector families indexed by $\mathrm{WRW}^{\le t}_s$ are written as records (number of vertices, vertices, coordinates), one per walk, in any order; operator families vertex by vertex, row-major.
--
--   The file also fixes the outputs of the explicit constructions (rotation table of a graph; generator bits of a Cayley graph), the input of the sparse SDP routine (sizes, positions and values of the listed nonzero entries, $\theta$, $\delta$), the Gram vectors it returns (stored row-major), and the input and the two output lists of the soft base decoder:
--   $$L_n=\{Z\in C_{\mathrm{base}}:\mathbb E_{i\sim[n]}[Z_iZ'_{\iota(i)}]\ge2\lambda\},\qquad L_A=\{Z\in C_{\mathrm{base}}:\mathbb E_{a\sim A}[Z_aZ'_a]\ge2\lambda\}.$$
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), pp. 8–19, 22, 28 (Propositions 1, 4–6, Claims 7, 12, Lemmas 1–3, Figures 2–4)

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_Decoder

namespace ExpanderWalkDecode.Main

open scoped Classical

/-!
# Input and output layouts of the algorithmic statements

Source: the algorithms of Propositions 1, 4, 5, 6, Claims 7 and 12, Lemmas 1–3 and Figures 2–4.
Each algorithmic statement runs one fixed program of `Machine` on an input written into its memory
banks, and reads its result from the output list. This file fixes the layouts.

Outer vertex sets are `Fin nA`. A port `x ∈ F₂^m` is coded as the number `∑_i x_i 2^i`, a block
likewise, and a latent point `(a, b, j)` of the walk with `t` edges as the mixed-radix number
`a + nA (code b + 2^{ms} code j)`.

The *walk structure* `(G, u, t)` is written as follows: integer bank `0` starts with
`nA, m, s, q, t` followed by the statement's own integer parameters; integer bank `1` holds the
rotation map (the neighbour of `v` along port `x` at address `2 (v 2^m + code x)`, the arrival port
code at the next address); integer bank `2` holds the generators (`code (u j i)` at `j s + i`);
integer bank `3` holds the embedding `ι` when there is one (`ι i` at address `i`). Real bank `0`
holds the statement's real scalars, real bank `1` the received word (`Y l` at the code of `l`),
real bank `2` the statement's real data list.
-/

/-- The number `∑_i x_i 2^i` coding `x ∈ F₂^m`. -/
def bitsToNat {m : ℕ} (x : Fin m → ZMod 2) : ℕ := ∑ i : Fin m, (x i).val * 2 ^ (i : ℕ)

/-- The code `∑_i code(b[i]) 2^{m i}` of an inner vertex. -/
def innerCode {m s : ℕ} (b : Inner m s) : ℕ := ∑ i : Fin s, bitsToNat (b i) * 2 ^ (m * (i : ℕ))

/-- The code `∑_i j_i q^i` of a generator-index vector. -/
def genCode {k q : ℕ} (js : Fin k → Fin q) : ℕ := ∑ i : Fin k, (js i : ℕ) * q ^ (i : ℕ)

/-- The code of a latent point (a code coordinate). -/
def latentIndex {nA m s q k : ℕ} (l : Latent (Fin nA) m s q k) : ℕ :=
  (l.1 : ℕ) + nA * (innerCode l.2.1 + 2 ^ (m * s) * genCode l.2.2)

/-- The bank holding `val x` at address `pos x` (and `0` at addresses not of this form). -/
noncomputable def placeAt {α β : Type} [Zero β] (pos : α → ℤ) (val : α → β) : ℤ → β :=
  fun z => if h : ∃ x, pos x = z then val h.choose else 0

section Layout

variable {nA m s q : ℕ}

/-- Integer bank `1`: the rotation map of the outer graph. -/
noncomputable def rotBank (G : RotGraph (Fin nA) (Fin m → ZMod 2)) : ℤ → ℤ :=
  placeAt (fun vpe : Fin nA × (Fin m → ZMod 2) × Fin 2 =>
      2 * ((vpe.1 : ℤ) * 2 ^ m + (bitsToNat vpe.2.1 : ℤ)) + (vpe.2.2 : ℤ))
    (fun vpe => if vpe.2.2 = 0 then ((G.nbr vpe.1 vpe.2.1 : ℕ) : ℤ)
      else (bitsToNat (G.rot (vpe.1, vpe.2.1)).2 : ℤ))

/-- Integer bank `2`: the generators of the inner Cayley graph. -/
noncomputable def genBank (u : Fin q → Inner m s) : ℤ → ℤ :=
  placeAt (fun ji : Fin q × Fin s => (ji.1 : ℤ) * s + (ji.2 : ℤ))
    (fun ji => (bitsToNat (u ji.1 ji.2) : ℤ))

/-- Integer bank `3`: the embedding `ι : [n] ↪ A`. -/
noncomputable def embBank {n : ℕ} (ι : Fin n ↪ Fin nA) : ℤ → ℤ :=
  placeAt (fun i : Fin n => (i : ℤ)) (fun i => ((ι i : ℕ) : ℤ))

/-- Real bank `1`: the received word on the code coordinates. -/
noncomputable def latentBank {t : ℕ} (Y : Latent (Fin nA) m s q t → ℝ) : ℤ → ℝ :=
  placeAt (fun l => (latentIndex l : ℤ)) Y

/-- The machine input carrying the walk structure `(G, u, t)`, the integer parameters `hdr`, the
embedding bank `emb`, the real scalars, the received-word bank and the real data list. -/
noncomputable def structInput (G : RotGraph (Fin nA) (Fin m → ZMod 2)) (u : Fin q → Inner m s)
    (t : ℕ) (hdr : List ℤ) (emb : ℤ → ℤ) (scalars : List ℝ) (Ybank : ℤ → ℝ) (data : List ℝ) :
    State :=
  init
    (fun k => if k = 0 then listBank scalars else if k = 1 then Ybank
      else if k = 2 then listBank data else fun _ => 0)
    (fun k => if k = 0 then listIBank ([(nA : ℤ), m, s, q, t] ++ hdr)
      else if k = 1 then rotBank G else if k = 2 then genBank u else if k = 3 then emb
      else fun _ => 0)

/-- A list of the walks of `WRW^{≤t}_s` in which every walk occurs exactly once. -/
def Enumerates {α : Type} (l : List α) : Prop := l.Nodup ∧ ∀ w, w ∈ l

/-- The record list of a vector family: for each walk of the enumeration `l`, its number of vertices,
its vertices, then the `d` coordinates of its vector. -/
def vectorRecords {G : RotGraph (Fin nA) (Fin m → ZMod 2)} {u : Fin q → Inner m s} {t d : ℕ}
    (l : List (WIdx G u t)) (x : WIdx G u t → Fin d → ℝ) : List ℝ :=
  l.flatMap fun w =>
    ((w.1.length : ℝ) :: w.1.map fun a => ((a : ℕ) : ℝ)) ++ List.ofFn (x w)

/-- `out` is the record list of the vector family `x` for some enumeration of `WRW^{≤t}_s`. -/
def EncodesVectors {G : RotGraph (Fin nA) (Fin m → ZMod 2)} {u : Fin q → Inner m s} {t d : ℕ}
    (out : List ℝ) (x : WIdx G u t → Fin d → ℝ) : Prop :=
  ∃ l : List (WIdx G u t), Enumerates l ∧ out = vectorRecords l x

/-- The operator family `{T_a}_{a ∈ A}`, vertex by vertex, each matrix row-major. -/
def opsList {d : ℕ} (T : Fin nA → Matrix (Fin d) (Fin d) ℝ) : List ℝ :=
  (List.finRange nA).flatMap fun a => (List.finRange d).flatMap fun i => List.ofFn fun j => T a i j

end Layout

/-- The rotation table of a graph on `Fin nA` with ports `Fin d`: `nA`, then for every vertex `v`
and port `i` (in increasing order) the pair `Rot (v, i)`. -/
def rotTableOut {nA d : ℕ} (G : RotGraph (Fin nA) (Fin d)) : List ℝ :=
  (nA : ℝ) :: (List.finRange nA).flatMap fun v => (List.finRange d).flatMap fun i =>
    [(((G.rot (v, i)).1 : ℕ) : ℝ), (((G.rot (v, i)).2 : ℕ) : ℝ)]

/-- The generators of a Cayley graph on `F₂^r`, each as `r` bits `0`/`1`. -/
def genOut {r q : ℕ} (u : Fin q → (Fin r → ZMod 2)) : List ℝ :=
  (List.finRange q).flatMap fun j => List.ofFn fun i => ((u j i).val : ℝ)

/-- The input `(a, b)` of two naturals, in integer bank `0` at addresses `0, 1`. -/
def natPairInput (a b : ℕ) : State :=
  init (fun _ _ => 0) (fun k => if k = 0 then listIBank [(a : ℤ), (b : ℤ)] else fun _ => 0)

/-- The `k` vectors of dimension `Δ` stored row-major in a list (`0` past its end). -/
def rowsOf (k Δ : ℕ) (out : List ℝ) : Fin k → Fin Δ → ℝ :=
  fun i j => out.getD ((i : ℕ) * Δ + j) 0

/-- The Gram matrix of a family of vectors indexed by `Fin k`. -/
def gramOf {k Δ : ℕ} (v : Fin k → Fin Δ → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => v i ⬝ᵥ v j

/-- The set `E` of `k × k` positive semidefinite matrices with diagonal at most `1`. -/
def EllK (k : ℕ) : Set (Matrix (Fin k) (Fin k) ℝ) := {Q | Q.PosSemidef ∧ ∀ i, Q i i ≤ 1}

/-- The input of the sparse SDP routine: integer bank `0` holds `k, m, L`; integer bank `1` holds
the positions `i₀, j₀, i₁, j₁, …` of the listed entries; real bank `0` holds `θ, δ`; real bank `1`
holds the values `A_{i₀ j₀}, A_{i₁ j₁}, …`. -/
noncomputable def sparseInput (k m : ℕ) (θ δ : ℝ) (A : Matrix (Fin k) (Fin k) ℝ)
    (entries : List (Fin k × Fin k)) : State :=
  init
    (fun b => if b = 0 then listBank [θ, δ]
      else if b = 1 then listBank (entries.map fun e => A e.1 e.2) else fun _ => 0)
    (fun b => if b = 0 then listIBank [(k : ℤ), (m : ℤ), (entries.length : ℤ)]
      else if b = 1 then listIBank (entries.flatMap fun e => [((e.1 : ℕ) : ℤ), ((e.2 : ℕ) : ℤ)])
      else fun _ => 0)

/-- The input of the soft base decoder: integer bank `0` holds `n, nA`; integer bank `3` holds the
embedding; real bank `0` holds `δ, λ`; real bank `2` holds `Z′_a` at address `a`. -/
noncomputable def softInput {n nA : ℕ} (ι : Fin n ↪ Fin nA) (δ lam : ℝ) (Z' : Fin nA → ℝ) : State :=
  init
    (fun b => if b = 0 then listBank [δ, lam]
      else if b = 2 then listBank (List.ofFn Z') else fun _ => 0)
    (fun b => if b = 0 then listIBank [(n : ℤ), (nA : ℤ)]
      else if b = 3 then embBank ι else fun _ => 0)

/-- The output of the soft decoder in the restated form (Appendix C.2):
`{Z ∈ C_base : E_{i ∼ [n]} [Z_i Z′_{ι(i)}] ≥ 2λ}`. -/
noncomputable def softListN {n nA : ℕ} (Cb : BinaryLinearCode n) (ι : Fin n ↪ Fin nA) (lam : ℝ)
    (Z' : Fin nA → ℝ) : Finset (Word n) :=
  Finset.univ.filter fun z => z ∈ Cb ∧ 2 * lam ≤ (n : ℝ)⁻¹ * ∑ i, sgn (z i) * Z' (ι i)

/-- The output of the soft decoder in the form of §4.3, on the padded word:
`{Z ∈ C_base : E_{a ∼ A} [Z_a Z′_a] ≥ 2λ}`. -/
noncomputable def softListA {n nA : ℕ} (Cb : BinaryLinearCode n) (ι : Fin n ↪ Fin nA) (lam : ℝ)
    (Z' : Fin nA → ℝ) : Finset (Word n) :=
  Finset.univ.filter fun z => z ∈ Cb ∧ 2 * lam ≤ avg fun a => pad ι z a * Z' a

end ExpanderWalkDecode.Main


