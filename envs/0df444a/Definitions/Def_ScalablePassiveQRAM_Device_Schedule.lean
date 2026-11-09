-- Prove2me | Definitions.Def_ScalablePassiveQRAM_Device_Schedule
-- name    : ScalablePassiveQRAM_Device_Schedule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:23:20.967523+00:00
-- url     : https://prove2.me/theorems/deb5cc57-f1c5-48ba-acd4-f67383473762
-- title:
--   The explicit load, query, and unload schedule
-- statement:
--   For an $n$-bit address, the device executes a fixed list of operations: load address bits in increasing order, query the memory, and unload in decreasing order. Every elementary operation records its exchange register or routing depth, direction, and allowed carrier flavors. The list and its prefix routing counts determine all layers and switch slices.
--
--   $$L=2n^2+4n+3,\qquad R_v=4(n-|v|)-2.$$
--
--   Address indices start at zero. The empty routing lists for the first bit are retained. This definition supplies the schedule shared by the physical Hamiltonian and its intended histories; it asserts no correctness property.
-- source:
--   Siddhartha Jain, Alexander Dalzell, Connor Hann, STOC 2027 submission #129 (October 2026), §§3.1–3.2, equations (12)–(17), pp.13–16. Canonical PDF SHA256 725dff5ab83fbe7e163da05440b75cc1d24f83804408cc139eb8954d2f8a076e.

import Mathlib

namespace ScalablePassiveQRAM.Device

/-- The dual-rail register exchanged with the carrier. Address indices are zero based. -/
inductive ExchangePort where
  | address (k : ℕ)
  | bus
  | switch (depth slice : ℕ)
  deriving DecidableEq, Repr

/-- One elementary operation of §3.2. `bit` selects {0,1}, otherwise {⋆}. -/
inductive Operation where
  | exchange (port : ExchangePort) (intoCarrier : Bool) (depth : ℕ)
  | route (depth : ℕ) (down bit : Bool)
  | read
  deriving DecidableEq, Repr

/-- Number of routing visits to a depth-d switch, equation (13). Used only at d<n. -/
def visits (n d : ℕ) : ℕ := 4 * (n - d) - 2

def load (k : ℕ) : List Operation :=
  [.exchange (.address k) true 0] ++
  ((List.range k).map fun d => .route d true true) ++
  [.exchange (.switch k 0) false k] ++
  ((List.range k).reverse.map fun d => .route d false false)

def query (n : ℕ) : List Operation :=
  [.exchange .bus true 0] ++
  ((List.range n).map fun d => .route d true true) ++ [.read] ++
  ((List.range n).reverse.map fun d => .route d false true) ++
  [.exchange .bus false 0]

def unload (n k : ℕ) : List Operation :=
  ((List.range k).map fun d => .route d true false) ++
  [.exchange (.switch k (visits n k)) true k] ++
  ((List.range k).reverse.map fun d => .route d false true) ++
  [.exchange (.address k) false 0]

/-- The source's load/query/reverse-load schedule, with all flavor sets explicit. -/
def schedule (n : ℕ) : List Operation :=
  (List.range n).flatMap load ++ query n ++
  (List.range n).reverse.flatMap (unload n)

def length (n : ℕ) : ℕ := (schedule n).length

def Operation.targetDepth (n : ℕ) : Operation → ℕ
  | .exchange _ _ d => d
  | .route d down _ => if down then d + 1 else d
  | .read => n

/-- Depth of the carrier after j steps; layer zero is the root. -/
def layerDepth (n j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | k + 1 => ((schedule n)[k]?).map (Operation.targetDepth n) |>.getD 0

/-- Slice used before the next routing visit to depth d. -/
def routeCount (n j d : ℕ) : ℕ :=
  ((schedule n).take j).countP fun op => match op with
    | .route e _ _ => e == d
    | _ => false

end ScalablePassiveQRAM.Device


