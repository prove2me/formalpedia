-- Prove2me | Definitions.Def_DistMapClust_Main_IO
-- name    : DistMapClust_Main_IO
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:05:30.60321+00:00
-- url     : https://prove2.me/theorems/2e654923-e74d-4f36-b6f1-e9620d3c4d5c
-- title:
--   Input and output layouts, size parameter and the §A.1 bound on OPT
-- statement:
--   How each problem is presented to the machine. The bit size $|I|$ has no meaning for opaque points and an infinite facility set, so the program receives a **size parameter** $s$ and the theorems require $n,k,d,\psi(,\tau)\le s$; $\mathrm{poly}(|I|)$ is read as $C s^e+C$. The paper's representation assumption §A.1(3), $2^{-\mathrm{poly}(|I|)}\le\mathrm{OPT}_I\le2^{\mathrm{poly}(|I|)}$, is
--   $$\mathrm{OptBounded}(s,c,\mathrm{OPT}_I):\qquad 2^{-s^c}\le\mathrm{OPT}_I\le 2^{s^c}$$
--   for a class constant $c$.
--
--   A clustering instance starts with $(n,k,d,\psi,s)$ in integer memory, the theorem's real parameters (e.g. $\chi,\varepsilon$) followed by the coefficients $c_{\ell,j,i}$ and, for row-wise ordered objectives, the weights in real memory, and the points of $P$ in point memory; its oracles are $\delta$, its Ball Intersection oracle, $f$, $f'$ and $\lambda$. A mapping-selection instance starts with $(n,k,d,\psi,\tau,s)$ and the types in integer memory and $\varepsilon$, the distances and the weights in real memory; its oracles are $f$, $f'$ and the $h_{t,\ell}$. A value-form instance $(P,U,W,f')$ with finite values gives $\varepsilon$, the values and the weights. Outputs are read from the halted state: centers in point cells $-1-i$; $\sigma(p)$ (0-based) in integer cell $-1-p$; a collection of $k$-tuples, of distance sets (with $\infty$ added), or of value-form instances through a count in integer cell $-1$ and the layouts documented in the file.
--
--   **Formalization Note.** `OptBounded`, `Instance.coefList`, `Instance.oracles`, `Instance.start`, `RowInstance.weightList`, `RowInstance.oracles`, `MapSelInstance.oracles`/`start`, `SelInstance.oracles`/`start`, `outCenters`, `ValidSel`, `outSel`, `outCount`, `outTuple`, `outSet`, `OutSetNonneg`, `outSelInstance`. Unused oracles are constant; mapping-selection problems use the point type `Unit`.
-- source:
--   Herold, Spoerhase, Kipouridis, Marx, A Unified Framework for Parameterized Approximation of Clustering Objectives via Distance Mappings, STOC 2027 submission (manuscript sha256 1d00c842…), p. 7 (Definition 1.1), pp. 8, 17 (Definitions 1.3, 1.8), p. 46 (§4), pp. 64–65 (§A.1)

import Mathlib
import Definitions.Def_DistMapClust_Main_Clustering
import Definitions.Def_DistMapClust_Main_Selection
import Definitions.Def_DistMapClust_Main_Machine

/-!
# Input and output layouts of the machine for the problems of the paper

Herold, Spoerhase, Kipouridis, Marx, *A Unified Framework for Parameterized Approximation of
Clustering Objectives via Distance Mappings*, STOC 2027 submission (manuscript sha256 1d00c842…):
Definition 1.1 (p. 7), Definitions 1.3 and 1.8 (pp. 8, 17), §4 (p. 46), §A.1 (pp. 64–65).

Encoding.
* Instance size. With opaque points and a possibly infinite facility set the bit size `|I|` has no
  meaning, so the program receives a size parameter `s` (in integer memory) and the theorems ask
  `n, k, d, ψ (, τ) ≤ s`; `poly(|I|)` is read as `C · s^e + C`. §A.1 assumption 3
  (`2^{−poly(|I|)} ≤ OPT_I ≤ 2^{poly(|I|)}`) is `OptBounded s c OPT_I` for a class constant `c`.
* Clustering input (`Instance.start`): integer memory `[n, k, d, ψ, s]` from cell `0`; real memory
  the list the theorem names (its parameters `χ`, `ε`, then `coefList` = `c_{ℓ,j,i}` in the order
  `ℓ, j, i`, then for row-wise instances `weightList` = `(wᵢ)_x` in the order `i, x`); point memory
  `P 0, …, P (n−1)` from cell `0`; every other point cell and every point register holds `P 0`.
  Oracles: `δ`, the instance's Ball Intersection oracle, `f` on a `d × n` matrix written row by row,
  for row-wise instances `f'` on a `d`-vector, and `λ`.
* Mapping-selection input (`MapSelInstance.start`): integer memory `[n, k, d, ψ, τ, s]` followed by
  `type(p)` (0-based) for `p = 0, …, n−1`; real memory `[ε]`, then `δ(xᵢ, p)` in the order `p, i`,
  then the weights; oracles `f` (the row-wise ordered norm), `f'` and `h_{t,ℓ}` (0-based `t, ℓ`).
  Value-form input (`SelInstance.start`): integer memory `[n, d, ψ, s]`, real memory `[ε]`, then the
  values `u(p, ℓ)ᵢ` in the order `p, ℓ, i`, then the weights; oracle `f'`.
* Unused oracles are constant (`0`, `[]`, `none`). Points of the mapping-selection problems are not
  needed by any instruction; their point type is `Unit`.
* Outputs, read from the halted state. Centers: `xᵢ` in point cell `−1 − i`. Selection: `σ(p)`
  (0-based) in integer cell `−1 − p`, valid when `0 ≤ σ(p) < ψ`. A collection of `k`-tuples: its size
  `M` in integer cell `−1`, center `i` of tuple `m` in point cell `−1 − (m k + i)`. A collection of
  distance sets: size `M` in integer cell `−1`; set `m` has its start address in integer cell
  `−2 − 2m` and its number of finite elements in integer cell `−3 − 2m`, the elements in the real
  cells from the start address on, and `∞` added. A list of value-form instances: size `M` in integer
  cell `−1`, instance `m` at the base address `B` in integer cell `−2 − m`, with `u'(p, ℓ)ᵢ` in real
  cell `B + (p ψ + ℓ) d + i` (and `∞` if integer cell `B + (p ψ + ℓ) d + i` is nonzero) and
  `(w'ᵢ)_x` in real cell `B + n ψ d + i n + x`; it has the same `n, d, ψ` and `f'` as the input.
-/

open scoped ENNReal

namespace DistMapClust.Main

/-- §A.1 assumption 3 with class constant `c` and size parameter `s`:
`2^{−s^c} ≤ OPT ≤ 2^{s^c}`. -/
def OptBounded (s c : ℕ) (opt : ℝ) : Prop :=
  (2 : ℝ) ^ (-((s : ℝ) ^ c)) ≤ opt ∧ opt ≤ (2 : ℝ) ^ ((s : ℝ) ^ c)

/-- The matrix whose entry `(j, p)` is entry `j n + p` of the list (row by row). -/
def listMat (d n : ℕ) (l : List ℝ) : Mat d n := fun j p => l.getD ((j : ℕ) * n + p) 0

/-- The vector whose entry `i` is entry `i` of the list. -/
def listVec (d : ℕ) (l : List ℝ) : Fin d → ℝ := fun i => l.getD i 0

namespace Instance

variable {α : Type} (I : Instance α)

/-- The coefficients `c_{ℓ,j,i}` in the order `ℓ, j, i`. -/
def coefList : List ℝ :=
  (List.finRange I.ψ).flatMap fun ℓ => (List.finRange I.d).flatMap fun j =>
    (List.finRange I.k).map fun i => I.coef ℓ j i

/-- The oracles of a clustering instance, with `λ` supplied by the theorem. -/
noncomputable def oracles (lam : ℝ → ℝ) : Oracles α where
  dist := I.δ
  ball := I.C
  obj := fun l => I.f (listMat I.d I.n l)
  norm := fun _ => 0
  map := fun _ _ _ => []
  lam := lam

/-- The start state on size parameter `s` and real input `reals`. -/
noncomputable def start (s : ℕ) (reals : List ℝ) : State α :=
  initState [(I.n : ℤ), I.k, I.d, I.ψ, s] reals (List.ofFn I.P) (I.P ⟨0, I.n_pos⟩)

end Instance

namespace RowInstance

variable {α : Type} (I : RowInstance α)

/-- The weights `(wᵢ)_x` in the order `i, x`. -/
def weightList : List ℝ :=
  (List.finRange I.d).flatMap fun i => (List.finRange I.n).map fun x => I.W i x

/-- The oracles of a row-wise ordered instance: those of the underlying instance and `f'`. -/
noncomputable def oracles (lam : ℝ → ℝ) : Oracles α :=
  { I.toInstance.oracles lam with norm := fun l => I.f' (listVec I.d l) }

end RowInstance

namespace MapSelInstance

variable (I : MapSelInstance)

/-- The oracles of a mapping-selection instance. -/
noncomputable def oracles : Oracles Unit where
  dist := fun _ _ => 0
  ball := fun _ _ => none
  obj := fun l => rowOrdNorm I.W I.f' (listMat I.d I.n l)
  norm := fun l => I.f' (listVec I.d l)
  map := fun t ℓ l =>
    if h : t < I.τ ∧ ℓ < I.ψ then List.ofFn (I.h ⟨t, h.1⟩ ⟨ℓ, h.2⟩ (listVec I.k l)) else []
  lam := fun _ => 0

/-- The start state on size parameter `s` and accuracy `ε`. -/
noncomputable def start (s : ℕ) (ε : ℝ) : State Unit :=
  initState ([(I.n : ℤ), I.k, I.d, I.ψ, I.τ, s] ++ List.ofFn fun p => ((I.type p : ℕ) : ℤ))
    ([ε] ++ ((List.finRange I.n).flatMap fun p => (List.finRange I.k).map fun i => I.δ p i) ++
      ((List.finRange I.d).flatMap fun i => (List.finRange I.n).map fun x => I.W i x))
    [] ()

end MapSelInstance

namespace SelInstance

variable (I : SelInstance)

/-- The oracles of a value-form instance: only `f'`. -/
noncomputable def oracles : Oracles Unit where
  dist := fun _ _ => 0
  ball := fun _ _ => none
  obj := fun _ => 0
  norm := fun l => I.f' (listVec I.d l)
  map := fun _ _ _ => []
  lam := fun _ => 0

/-- The start state on size parameter `s` and accuracy `ε` (values written as reals; used for
instances whose values are all finite). -/
noncomputable def start (s : ℕ) (ε : ℝ) : State Unit :=
  initState [(I.n : ℤ), I.d, I.ψ, s]
    ([ε] ++ ((List.finRange I.n).flatMap fun p => (List.finRange I.ψ).flatMap fun ℓ =>
        (List.finRange I.d).map fun i => (I.U p ℓ i).toReal) ++
      ((List.finRange I.d).flatMap fun i => (List.finRange I.n).map fun x => I.W i x))
    [] ()

end SelInstance

section Output

variable {α : Type}

/-- Output center `i`: point cell `−1 − i`. -/
def outCenters (S : State α) (k : ℕ) : Fin k → α := fun i => S.ptMem (-1 - (i : ℤ))

/-- The integer in the output cell of point `p`: integer cell `−1 − p`. -/
def outSelVal (S : State α) (p : ℕ) : ℤ := S.intMem (-1 - (p : ℤ))

/-- The output selection is valid: `0 ≤ σ(p) < ψ` for every point `p < n`. -/
def ValidSel (S : State α) (n ψ : ℕ) : Prop :=
  ∀ p < n, 0 ≤ outSelVal S p ∧ outSelVal S p < ψ

/-- The output selection (meaningful when `ValidSel`). -/
def outSel (S : State α) (n ψ : ℕ) (hψ : 0 < ψ) : Fin n → Fin ψ :=
  fun p => ⟨(outSelVal S p).toNat % ψ, Nat.mod_lt _ hψ⟩

/-- The number of output items: integer cell `−1`. -/
def outCount (S : State α) : ℕ := (S.intMem (-1)).toNat

/-- Output `k`-tuple number `m`: center `i` in point cell `−1 − (m k + i)`. -/
def outTuple (S : State α) (k m : ℕ) : Fin k → α :=
  fun i => S.ptMem (-1 - ((m * k + i : ℕ) : ℤ))

/-- Start address of output distance set `m`: integer cell `−2 − 2m`. -/
def outSetStart (S : State α) (m : ℕ) : ℤ := S.intMem (-2 - 2 * (m : ℤ))

/-- Number of finite elements of output distance set `m`: integer cell `−3 − 2m`. -/
def outSetLen (S : State α) (m : ℕ) : ℕ := (S.intMem (-3 - 2 * (m : ℤ))).toNat

/-- The finite elements of output distance set `m` are nonnegative reals. -/
def OutSetNonneg (S : State α) (m : ℕ) : Prop :=
  ∀ t : ℕ, t < outSetLen S m → 0 ≤ S.core.mem (outSetStart S m + (t : ℤ))

/-- Output distance set `m`, as a finite subset of `R̄ = ℝ≥0∞`, with `∞` added. -/
noncomputable def outSet (S : State α) (m : ℕ) : Finset ℝ≥0∞ :=
  insert ⊤ ((Finset.range (outSetLen S m)).image
    fun t : ℕ => ENNReal.ofReal (S.core.mem (outSetStart S m + (t : ℤ))))

/-- Output value-form instance number `m`; same `n, d, ψ` and `f'` as `I`. -/
noncomputable def outSelInstance (S : State α) (I : SelInstance) (m : ℕ) : SelInstance :=
  let B : ℤ := S.intMem (-2 - (m : ℤ))
  { n := I.n, d := I.d, ψ := I.ψ, n_pos := I.n_pos, d_pos := I.d_pos, ψ_pos := I.ψ_pos,
    U := fun p ℓ i =>
      let idx : ℤ := (((p : ℕ) * I.ψ + ℓ) * I.d + i : ℕ)
      if S.intMem (B + idx) ≠ 0 then ⊤ else ENNReal.ofReal (S.core.mem (B + idx)),
    W := fun i x => S.core.mem (B + ((I.n * I.ψ * I.d + (i : ℕ) * I.n + x : ℕ) : ℤ)),
    f' := I.f' }

end Output

end DistMapClust.Main


